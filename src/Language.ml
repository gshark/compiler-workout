(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let rec my_init i n f = if i < n then (f i)::(my_init (i + 1) n f) else []
    let list_init n f = my_init 0 n f

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = list_init   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
 
let pack lst = match lst with
| Some l -> l
| None -> []
   
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
    let bool_to_int boolean = if boolean then 1 else 0

    let calculate_binop op lval rval = match op with
      | "+" -> lval + rval
      | "-" -> lval - rval
      | "*" -> lval * rval
      | "/" -> lval / rval
      | "%" -> lval mod rval
      | "<" -> bool_to_int(lval < rval)
      | ">" -> bool_to_int(lval > rval)
      | "<=" -> bool_to_int(lval <= rval)
      | ">=" -> bool_to_int(lval >= rval)
      | "==" -> bool_to_int(lval == rval)
      | "!=" -> bool_to_int(lval != rval)
      | "&&" -> bool_to_int((lval != 0) && (rval != 0))
      | "!!" -> bool_to_int((lval != 0) || (rval != 0))
      | _ -> failwith ("Unsupported binary operation '" ^ op ^ "'")                                                 
    
let rec eval env ((s, i, o, r) as conf) exp = match exp with
    | Const c -> (s, i, o, Some (Value.of_int c))
    | Var name -> (s, i, o, Some (State.eval s name))
    | Binop (op, l, r) -> 
      let ((_, _, _, Some lval) as conf') = eval env conf l in
      let (s', i', o', Some rval) = eval env conf' r in 
      let res = calculate_binop op (Value.to_int lval) (Value.to_int rval) in
      (s', i', o', Some (Value.of_int res))
    | Call (name, args) -> 
      let (_, _, _, evaluated_args) = eval_list env conf args in
      (env#definition env name evaluated_args conf)
    | Array a -> 
      let (s', i', o', res) = eval_list env conf a in
      (s', i', o', Some (Value.of_array res))
    | Sexp (s, v) ->
      let (s', i', o', res) = eval_list env conf v in
      (s', i', o', Some (Value.sexp s res))
    | String str -> (s, i, o, Some (Value.of_string str))
    | Elem (e, id) ->
      let (s', i', o', Some evaluated_id) = eval env conf id in
      let (s'', i'', o'', Some obj) = eval env (s', i', o', None) e in
      let n = Value.to_int evaluated_id in
      let res = (match obj with
        | Value.Array arr -> List.nth arr n
        | Value.String str -> let chr = String.get str n in 
          Value.of_int (Char.code chr)) in
      (s'', i'', o'', Some res)
    | Length e ->
      let (s', i', o', Some obj) = eval env conf e in
      let res = (match obj with
        | Value.Array arr -> List.length arr
        | Value.String str -> String.length str) in
      (s', i', o', Some (Value.of_int res))
    | _ -> failwith "Unsupported pattern"
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)       

         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    let make_op op = (ostap ($(op)), fun x y -> Binop(op, x, y))

    ostap (
      parse: expr;

      expr:
        !(Ostap.Util.expr                              
           (fun x -> x)                          
           [|
            `Lefta , [make_op "!!"];
            `Lefta , [make_op "&&"];
            `Nona ,  [make_op "<="; make_op ">="; make_op "<"; make_op ">"; make_op "=="; make_op "!="];                           
            `Lefta , [make_op "+"; make_op "-"];
            `Lefta, [make_op "*"; make_op "/"; make_op "%"]; 
           |]                        
           secondary                   
         );
      
      secondary:
        e: primary 
        f:( "[" id:parse "]" {`Elem id}
          | "." "length" {`Length})*
        {List.fold_left (fun e f -> match f with
          | `Elem id -> Elem (e, id)
          | `Length -> Length e
          ) e f};
      
      primary: 
        n:DECIMAL {Const n}      
      | c:CHAR {Const (Char.code c)}
      | s:STRING {String (String.sub s 1 ((String.length s) - 2))}
      | "`" name:IDENT args:(-"(" !(Util.list parse) -")")? {Sexp (name, pack args)}
      | "[" arr:!(Util.list0 parse) "]" {Array arr}  
      | name:IDENT "(" args:!(Util.list0)[parse] ")" {Call (name, args)}
      | x:IDENT {Var x} 
      | -"(" expr -")"
      
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
        parse:
            "`" pt:IDENT args:(-"(" !(Util.list parse) -")")? {Sexp (pt, pack args)}
          | "_" {Wildcard}
          | i:IDENT {Ident i}
         )
        
        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
        
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let merge_k st2 k = match k with
    | Skip -> st2
    | k' -> Seq(st2, k') 

    let rec match_ pt vl = match pt with
    | Pattern.Wildcard | Pattern.Ident _ -> true
    | Pattern.Sexp (t, ps) -> (match vl with
      | Value.Sexp (vt, vs)-> 
        (t = vt && List.for_all2 match_ ps vs)
      | _ -> false)

    let rec unpack_sexp (s, x) pt v = match pt with
    | Pattern.Wildcard -> s, x
    | Pattern.Ident i -> (fun q -> if i = q then v else s q), i::x
    | Pattern.Sexp (t, ps) -> (match v with
      | Value.Sexp (vt, vs) -> List.fold_left2 unpack_sexp (s, x) ps vs
      | _ -> failwith "Incorrect value")

    let rec eval env ((s, i, o, r) as conf) k st = match st with
        | Assign (x, id, e) -> 
          let (s', i', o', Some evaluated_e) = Expr.eval env conf e in 
          let (s'', i'', o'', evaluated_id) = Expr.eval_list env (s', i', o', None) id in
          eval env (update s'' x evaluated_e evaluated_id, i'', o'', None) Skip k
        | Seq (st1, st2) -> 
          let k' = merge_k st2 k in
          eval env conf k' st1
        | Skip -> (match k with
          | Skip -> (s, i, o, None)
          | _ -> eval env (s, i, o, r) Skip k)
        | If (cond, then_, else_) -> 
          let (s', i', o', Some evaluated_cond) = Expr.eval env conf cond in
          eval env (s', i', o', None) k (if (Value.to_int evaluated_cond) <> 0 then then_ else else_)
        | While (cond, do_) -> 
          let (s', i', o', Some evaluated_cond) = Expr.eval env conf cond in
          if ((Value.to_int evaluated_cond) = 0) 
          then 
            eval env (s', i', o', None) Skip k 
          else let k' = merge_k st k in
            eval env (s', i', o', None) k' do_
        | Repeat (do_, cond) -> 
          let cond' = Expr.Binop ("==", cond, Expr.Const 0) in 
          let while_ = While (cond', do_) in 
          let k' = merge_k while_ k in
          eval env (s, i, o, None) k' do_
        | Call (name, args) -> 
          let conf' = Expr.eval env conf (Expr.Call (name, args)) in
          eval env conf' Skip k
        | Return x -> (match x with
          | None -> (s, i, o, None)
          | Some x' -> Expr.eval env conf x')
        | Leave -> let s' = State.drop s in 
          eval env (s', i, o, None) Skip k
        | Case (cond, cases) ->
          let (s', i', o', Some evaluated_cond) = Expr.eval env conf cond in
          let rec do_swith cond cases = (match cases with
            | [] -> eval env conf Skip k 
            | (pt, args)::others -> 
              if match_ pt cond 
              then 
                let s_, x = unpack_sexp (State.undefined, []) pt cond in
                let s' = State.push s s_ x in
                let k' = merge_k Leave k in 
                eval env (s', i, o, None) k' args  
              else
                do_swith cond others
            ) in 
            do_swith evaluated_cond cases
        | _ -> failwith "Unsupported pattern"
                                                       

     
    (* Statement parser *)
    let rec parse_else elif_ else_ = match elif_ with
    | [] -> (match else_ with
        | None -> Skip
        | Some text -> text)
    | (cond, then_)::tail -> If (cond, then_, parse_else tail else_)
    
    ostap (
      parse: 
          st1:stmt ";" st2:parse {Seq (st1, st2)}
        | stmt; 

      stmt: 
          %"skip" {Skip}
        | %"while" cond:!(Expr.parse) %"do" do_:parse %"od" {While (cond, do_)}
        | %"repeat" do_:parse %"until" cond:!(Expr.parse) {Repeat (do_, cond)}
        | %"for" init:parse "," cond:!(Expr.parse) "," inc:parse %"do" do_:parse %"od" {Seq (init, While (cond, Seq (do_, inc)))}
        | %"if" cond:!(Expr.parse) %"then" then_:parse elif_:(%"elif" !(Expr.parse) %"then" parse)* else_:(%"else" parse)? %"fi" 
            {If (cond, then_, parse_else elif_ else_)} 
        | %"case" cond:!(Expr.parse) %"of"
            cases:!(Util.listBy)[ostap ("|")][ostap (!(Pattern.parse) -"->" parse)]
          %"esac" {Case (cond, cases)}
        | %"return" x:(!(Expr.parse))? {Return x}
        | x:IDENT id:(-"[" !(Expr.parse) -"]")* ":=" e:!(Expr.parse) {Assign (x, id, e)}      
        | name:IDENT "(" args:(!(Util.list)[ostap (!(Expr.parse))])? ")" {Call (name, pack args)}
    )
      
  end
   

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)

type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
