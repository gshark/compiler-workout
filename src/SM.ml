open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
          
let rec eval env ((cstack, stack, ((s, i, o) as c)) as conf) p = match p with
| [] -> conf
| cur::next -> (match cur with
    
    | BINOP op -> (match stack with
        | y::x::tail -> 
            let res = Value.of_int (Expr.calculate_binop op (Value.to_int x) (Value.to_int y)) in 
            eval env (cstack, res::tail, (s, i, o)) next 
        | _ -> failwith "Stack size less than 2")
    | CONST c -> eval env (cstack, (Value.of_int c)::stack, (s, i, o)) next
    | STRING str -> eval env (cstack, (Value.of_string str)::stack, (s, i, o)) next
    | LD x -> let v = State.eval s x in eval env (cstack, v::stack, (s, i, o)) next
    | ST x -> (match stack with
        | v::tail -> eval env (cstack, tail, (State.update x v s, i, o)) next
        | _ -> failwith "Empty stack")
    | STA (x, n) -> let v::tail, stack' = split (n + 1) stack in (match stack with
        | v::tail -> eval env (cstack, stack', (Stmt.update s x v (List.rev tail), i, o)) next
        | _ -> failwith "Empty stack")
    | LABEL l -> eval env (cstack, stack, (s, i, o)) next
    | JMP label -> eval env (cstack, stack, (s, i, o)) (env#labeled label)
    | CJMP (cond, label) -> (match stack with
        | (Value.Int x)::tail -> eval env (cstack, tail, (s, i, o)) (
            let cond' = if cond = "nz" then x <> 0 else x = 0
            in if cond' then (env#labeled label) else next)
        | _ -> failwith "Empty stack")
    | CALL (f, n, args) -> 
        if env#is_label f then 
          let cstack' = (next, s)::cstack in 
          eval env (cstack', stack, (s, i, o)) (env#labeled f)
        else
          eval env (env#builtin conf f n args) next
    | BEGIN (_, args, locals) -> 
        let init_state = State.enter s (args@locals) in
        let state_updater = fun x (s, v::tail) -> (State.update x v s, tail) in
        let (s', stack') = List.fold_right state_updater args (init_state, stack) in
        eval env (cstack, stack', (s', i, o)) next
    | END | RET _ -> (match cstack with
        | [] -> conf
        | (next', s')::cstack' ->  eval env (cstack', stack, (State.leave s s', i, o)) next')
    | SEXP (t, n) -> let taken, stack' = split n stack in
      let v = Value.sexp t (List.rev taken) in 
      let stack'' = v::stack' in
      eval env (cstack, stack'', (s, i, o)) next
    | DROP -> let v::stack' = stack in 
      eval env (cstack, stack', (s, i, o)) next
    | DUP -> let v::stack' = stack in
      eval env (cstack, v::stack, (s, i, o)) next
    | SWAP -> let v::v'::stack' = stack in
      eval env (cstack, v'::v::stack', (s, i, o)) next
    | ENTER st -> let s' = State.push s State.undefined st in
      eval env (cstack, stack, (s', i, o)) next
    | LEAVE -> let s' = State.drop s in
      eval env (cstack, stack, (s', i, o)) next
    | TAG t -> let v::stack' = stack in
      let v' = Value.of_int (match v with
        | Value.Sexp (st, sv) -> if st = t then 1 else 0 
        | _ -> 0) in
      eval env (cstack, v'::stack', (s, i, o)) next
   | _ -> failwith "Unsupported pattern")

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

class env = 
    object (self)
        val mutable cnt = 0
        method new_label = cnt <- cnt + 1; Printf.sprintf "L%d" cnt
    end

let rec my_init i n f = if i < n then (f i)::(my_init (i + 1) n f) else []
let list_init n f = my_init 0 n f

let get_label name = "L" ^ name

let rec pattern_depth pt = match pt with
| Stmt.Pattern.Wildcard | Stmt.Pattern.Ident _ -> 1
| Stmt.Pattern.Sexp (s, xs) -> 1 + (List.fold_left max 0 (List.map pattern_depth xs))

let rec pattern_compile pt stacked n = match pt with
| Stmt.Pattern.Wildcard | Stmt.Pattern.Ident _ -> [DROP]
| Stmt.Pattern.Sexp (t, xs) -> 
  let call_elem i pt_ = [DUP; CONST i; CALL (get_label ".elem", 2, false)] @ 
    (pattern_compile pt_ (stacked + 1) n) in
  [DUP; TAG t; CJMP ("z", List.nth n stacked)] @
  (List.concat (List.mapi call_elem xs)) @ 
  [DROP]

let rec bind_compile pt vars = match pt with
| Stmt.Pattern.Wildcard -> vars, [DROP]
| Stmt.Pattern.Ident i -> i::vars, [ST i]
| Stmt.Pattern.Sexp (t, xs) ->
  let make_pair a b = (a, b) in
  let bind (v, p) (c, patt) = 
    let v', p' = bind_compile patt v in
    v', (p @ [DUP; CONST c; CALL (get_label ".elem", 2, false)] @ p') in 
  let vars', p = List.fold_left bind (vars, []) (List.mapi make_pair xs) in
  vars', p @ [DROP]
  
let rec expr_compile exp = match exp with
| Expr.Var name -> [LD name]
| Expr.Const x -> [CONST x]
| Expr.String s -> [STRING s]
| Expr.Array a -> 
  let compiled_a = List.concat (List.map expr_compile a) in
  compiled_a @ [CALL (get_label ".array", List.length a, false)]
| Expr.Binop (op, x, y) -> expr_compile x @ expr_compile y @ [BINOP op]
| Expr.Call (name, args) ->  
    let compiled_args = List.concat (List.map expr_compile args) in 
    compiled_args @ [CALL (get_label name, List.length args, false)]
| Expr.Elem (a, id) -> let compiled_a = expr_compile a in
  let compiled_id = expr_compile id in
  compiled_a @ compiled_id @ [CALL (get_label ".elem", 2, false)]
| Expr.Length a -> let compiled_a = expr_compile a in
  compiled_a @ [CALL (get_label ".length", 1, false)]  
| Expr.Sexp (t, xs) -> (List.concat (List.map expr_compile xs)) @ [SEXP (t, List.length xs)]

let rec stmt_compile env to_drop end_label st = 
  let rec call f args p =
    let args_code = List.concat @@ List.map expr_compile args in
    args_code @ [CALL (get_label f, List.length args, p)] in
match st with

| Stmt.Assign (x, id, e) -> false, (match id with 
  | [] -> expr_compile e @ [ST x]
  | idl -> let compiled_id = List.concat (List.map expr_compile idl) in
          compiled_id @ expr_compile e @ [STA (x, List.length idl)])
| Stmt.Seq (s1, s2) -> 
  let f1, p1 = stmt_compile env to_drop end_label s1 in 
  let f2, p2 = stmt_compile env to_drop end_label s2 in
  f1 || f2, p1 @ p2
| Stmt.Skip -> false, []
| Stmt.If (cond, then_, else_) -> 
    let cond' = expr_compile cond in
    let label_else = env#new_label in
    let label_fi = env#new_label in
    let fth, compiled_then = stmt_compile env to_drop end_label then_ in
    let fel, compiled_else = stmt_compile env to_drop end_label else_ in
    fth || fel, 
    cond' @ [CJMP ("z", label_else)] @ compiled_then @ [JMP label_fi] @ [LABEL label_else] @ compiled_else @ [LABEL label_fi]
| Stmt.While (cond, do_) -> 
    let cond' = expr_compile cond in
    let label_do = env#new_label in
    let label_od = env#new_label in
    let f, compiled_do = stmt_compile env to_drop end_label do_ in
    f, [LABEL label_do] @ cond' @ [CJMP ("z", label_od)] @ compiled_do @ [JMP label_do] @ [LABEL label_od]
| Stmt.Repeat (do_, cond) ->
    let cond' = expr_compile cond in
    let label_repeat = env#new_label in
    let f, compiled_do = stmt_compile env to_drop end_label do_ in
    f, [LABEL label_repeat] @ compiled_do @ cond' @ [CJMP ("z", label_repeat)]
| Stmt.Call (name, args) ->
    let compiled_args = List.concat (List.map expr_compile args) in 
    false, compiled_args @ [CALL (get_label name, List.length args, true)]
| Stmt.Return x -> false,  (list_init to_drop (fun x -> DROP)) @ (match x with
    | None -> [RET false]
    | Some x' -> (expr_compile x') @ [RET true])
| Stmt.Case (cond, cases) ->
  let end_label = env#new_label in
  let compiled_cond = expr_compile cond in
  let compile_case (pt, args) end_label = 
    let depth = pattern_depth pt in
    let labels = list_init (depth + 1) (fun _ -> env#new_label) in
    let drop_labels = List.rev (List.tl (List.concat (List.map (fun l -> [DROP; LABEL l]) labels))) in
    let f, xs = stmt_compile env (to_drop + 1) end_label args in 
    let enter_bind p =
      let vars, p' = bind_compile p [] in
      (ENTER vars)::p' in
    [DUP] @ pattern_compile pt 1 labels @ [DUP] @ enter_bind pt @ xs @ [LEAVE; JMP end_label] @ drop_labels in
  let compiled_cases = List.map (fun c -> compile_case c end_label) cases in
  false, compiled_cond @ (List.concat compiled_cases) @ [LABEL end_label; DROP]  
| _ -> failwith "Unsupported pattern"


(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

let def_compile env (name, (args, locals, body)) =
  let end_label = env#new_label in
  let f, p = stmt_compile env 0 end_label body in
  let pl = if f then [LABEL end_label] else [] in
  env,  [LABEL name; BEGIN (name, args, locals)] @ p @ pl @ [END]

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) = let env = new env in
    let add_compiled (env, p) (name, others) = 
      let env, p' = def_compile env (get_label name, others) in 
      env, p'::p in 
    let env, compiled_defs = List.fold_left add_compiled (env, []) defs in 
    let end_label = env#new_label in
    let f, main = stmt_compile env 0 end_label p in
    let pl = if f then [LABEL end_label] else [] in
    main @ pl @ [END] @ (List.concat compiled_defs)
