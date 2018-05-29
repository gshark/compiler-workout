open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
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
    | _ -> failwith "Unsupported pattern")

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
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
        method new_label = cnt <- cnt + 1; Printf.sprintf "generated_label_%d" cnt
    end

let rec expr_compile exp = match exp with
| Expr.Var name -> [LD name]
| Expr.Const x -> [CONST x]
| Expr.String s -> [STRING s]
| Expr.Array a -> 
  let compiled_a = List.map expr_compile a in
  List.concat compiled_a @ [CALL ("$array", List.length a, false)]
| Expr.Binop (op, x, y) -> expr_compile x @ expr_compile y @ [BINOP op]
| Expr.Call (name, args) ->  
    let compiled_args = List.concat (List.map expr_compile args) in 
    compiled_args @ [CALL (name, List.length args, false)]
| Expr.Elem (a, id) -> let compiled_a = expr_compile a in
  let compiled_id = expr_compile id in
  compiled_a @ compiled_id @ [CALL ("$elem", 2, false)]
| Expr.Length a -> let compiled_a = expr_compile a in
  compiled_a @ [CALL ("$length", 1, false)]  
| _ -> failwith "Unsupported pattern"

let rec stmt_compile env st = match st with
| Stmt.Assign (x, id, e) -> (match id with 
  | [] -> expr_compile e @ [ST x]
  | idl -> let compiled_id = List.concat (List.map expr_compile idl) in
          compiled_id @ expr_compile e @ [STA (x, List.length idl)])
| Stmt.Seq (s1, s2) -> stmt_compile env s1 @ stmt_compile env s2
| Stmt.Skip -> []
| Stmt.If (cond, then_, else_) -> 
    let cond' = expr_compile cond in
    let label_else = env#new_label in
    let label_fi = env#new_label in
    let compiled_then = stmt_compile env then_ in
    let compiled_else = stmt_compile env else_ in
    cond' @ [CJMP ("z", label_else)] @ compiled_then @ [JMP label_fi] @ [LABEL label_else] @ compiled_else @ [LABEL label_fi]
| Stmt.While (cond, do_) -> 
    let cond' = expr_compile cond in
    let label_do = env#new_label in
    let label_od = env#new_label in
    let compiled_do = stmt_compile env do_ in
    [LABEL label_do] @ cond' @ [CJMP ("z", label_od)] @ compiled_do @ [JMP label_do] @ [LABEL label_od]
| Stmt.Repeat (do_, cond) ->
    let cond' = expr_compile cond in
    let label_repeat = env#new_label in
    let compiled_do = stmt_compile env do_ in
    [LABEL label_repeat] @ compiled_do @ cond' @ [CJMP ("z", label_repeat)]
| Stmt.Call (name, args) ->
    let compiled_args = List.concat (List.map expr_compile args) in 
    compiled_args @ [CALL (name, List.length args, true)]
| Stmt.Return x -> (match x with
    | None -> [RET false]
    | Some x' -> (expr_compile x') @ [RET true])
| _ -> failwith "Unsupported pattern"

let def_compile env (name, (args, locals, body)) = 
    [LABEL name; BEGIN (name, args, locals)] @ (stmt_compile env body) @ [END]

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) = let env = new env in
    let add_compiled ls def = ls @ (def_compile env def) in 
    let compiled_defs = List.fold_left add_compiled [] defs in 
    let main = stmt_compile env p in
    main @ [END] @ compiled_defs
