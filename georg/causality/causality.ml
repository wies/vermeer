type variable_type = Boolean | Int;;
type variable_term = Var of string * variable_type;;
type const_term = Const of int;;
type rel_op = EQ | NEQ | GT | LT;;
type relation_term = Relation of rel_op * variable_term * const_term;;
type boolean_term = 
| BoolVar of variable_term
| And of variable_term * variable_term
| Not of variable_term
;;
type function_term = BoolFunction of relation_term | IntFunction of variable_term | ConstIntFunction of const_term | ITE of boolean_term * variable_term * variable_term;;

let compare_vars = fun v1 v2 ->
match v1, v2 with
| Var(n1, _), Var(n2, _) -> String.compare n1 n2
;;

module VarMap = Map.Make(struct type t = variable_term let compare = compare_vars end);;

type causal_model_type = CausalModel of variable_term list * variable_term list * (function_term VarMap.t);;

type situation_type = Situation of causal_model_type * (const_term VarMap.t);;

let print_variable = fun var ->
match var with
| Var(name, _) -> print_string("    " ^ name ^ "\n"); ()
;;

let print_assignment = fun var value ->
match var, value with
| Var(name, _), Const(v) -> print_string("    "); print_string(name); print_string(" = "); print_int(v); print_string("\n"); ()
;;

let print_equation = fun var value ->
match var, value with
| Var(name, _), BoolFunction(Relation(EQ, Var(name2, _), Const(v))) -> print_string("    " ^ name ^ " <- " ^ name2 ^ " = "); print_int(v); print_string("\n"); ()
| Var(name, _), BoolFunction(Relation(NEQ, Var(name2, _), Const(v))) -> print_string("    " ^ name ^ " <- " ^ name2 ^ " != "); print_int(v); print_string("\n"); ()
| Var(name, _), BoolFunction(Relation(GT, Var(name2, _), Const(v))) -> print_string("    " ^ name ^ " <- " ^ name2 ^ " > "); print_int(v); print_string("\n"); ()
| Var(name, _), BoolFunction(Relation(LT, Var(name2, _), Const(v))) -> print_string("    " ^ name ^ " <- " ^ name2 ^ " < "); print_int(v); print_string("\n"); ()
| Var(name, _), IntFunction(Var(name2, _)) -> print_string("    " ^ name ^ " <- " ^ name2 ^ "\n"); ()
| Var(name, _), ConstIntFunction(Const(c)) -> print_string("    " ^ name ^ " <- "); print_int(c); print_string("\n"); ()
| Var(name, _), ITE(BoolVar(Var(name2, _)), Var(v1, _), Var(v2, _)) -> print_string("    " ^ name ^ " <- if (" ^ name2 ^ ") then " ^ v1 ^ " else " ^ v2 ^ "\n"); ()
| Var(name, _), ITE(And(Var(v1, _), Var(v2, _)), Var(v3, _), Var(v4, _)) -> print_string("    " ^ name ^ " <- if (" ^ v1 ^ " and " ^ v2 ^ ") then " ^ v3 ^ " else " ^ v4 ^ "\n"); ()
| Var(name, _), ITE(Not(Var(v1, _)), Var(v2, _), Var(v3, _)) -> print_string("    " ^ name ^ " <- if (not(" ^ v1 ^ ")) then " ^ v2 ^ " else " ^ v3 ^ "\n"); ()
;;

let print_situation = fun s ->
match s with
| Situation(CausalModel(exogenous_variables, endogenous_variables, equations), context) -> 
print_string("[\n"); 
print_string("  exogenous variables: {\n"); 
List.iter print_variable exogenous_variables; 
print_string("  }\n"); 
print_string("  endogenous variables: {\n"); 
List.iter print_variable endogenous_variables; 
print_string("  }\n"); 
print_string("  structural equations: {\n"); 
VarMap.iter print_equation equations; 
print_string("  }\n"); 
print_string("  context: {\n"); 
VarMap.iter print_assignment context; 
print_string("  }\n"); 
print_string("]\n"); ()
;;

let modify_model = fun m var value ->
match m with
| CausalModel(exogenous_variables, endogenous_variables, equations) -> let equs = VarMap.add var value equations in CausalModel(exogenous_variables, endogenous_variables, equs)
;;

let variable_to_smt2 = fun var ->
match var with
| Var(name, Int) -> "(declare-fun " ^ name ^ " () Int)" 
| Var(name, Boolean) -> "(declare-fun " ^ name ^ " () Bool)" 
;;

let int_to_smt2 = fun c ->
if c < 0 
then 
  ("(- " ^ Pervasives.string_of_int(abs(c)) ^ ")")
else 
  (Pervasives.string_of_int(c))
;;

let equation_to_smt2 = fun var f ->
match var with
| Var(var_name, _) ->
(
match f with
| ConstIntFunction(Const(c)) -> "(assert (= " ^ var_name ^ " " ^ int_to_smt2(c) ^ "))"
| IntFunction(Var(v, _)) -> "(assert (= " ^ var_name ^ " " ^ v ^ "))"
| BoolFunction(Relation(EQ, Var(name2, _), Const(v))) -> "(assert (= " ^ var_name ^ " (= " ^ name2 ^ " " ^ string_of_int(v) ^ ")))"
| BoolFunction(Relation(NEQ, Var(name2, _), Const(v))) -> "(assert (= " ^ var_name ^ " (not (= " ^ name2 ^ " " ^ string_of_int(v) ^ "))))"
| BoolFunction(Relation(GT, Var(name2, _), Const(v))) -> "(assert (= " ^ var_name ^ " (> " ^ name2 ^ " " ^ string_of_int(v) ^ ")))"
| BoolFunction(Relation(LT, Var(name2, _), Const(v))) -> "(assert (= " ^ var_name ^ " (< " ^ name2 ^ " " ^ string_of_int(v) ^ ")))"
| ITE(BoolVar(Var(name2, _)), Var(v1, _), Var(v2, _)) -> "(assert (= " ^ var_name ^ " (ite " ^ name2 ^ " " ^ v1 ^ " " ^ v2 ^ ")))"
| ITE(And(Var(v1, _), Var(v2, _)), Var(v3, _), Var(v4, _)) -> "(assert (= " ^ var_name ^ " (ite (and " ^ v1 ^ " " ^ v2 ^ ") " ^ v3 ^ " " ^ v4 ^ ")))"
| ITE(Not(Var(v1, _)), Var(v2, _), Var(v3, _)) -> "(assert (= " ^ var_name ^ " (ite (not " ^ v1 ^ ") " ^ v2 ^ " " ^ v3 ^ ")))"
);; 

let print_variable_name = fun v ->
match v with
| Var(name, _) -> print_string(name ^ " ")
;;

let model_to_smt2 = fun m ->
match m with
| CausalModel(exogenous_variables, endogenous_variables, equations) -> 
let l_exogenous_variables = List.map variable_to_smt2 exogenous_variables in
let l_endogenous_variables = List.map variable_to_smt2 endogenous_variables in
let l_equations = VarMap.fold (fun var f lold -> (equation_to_smt2 var f) :: lold) equations [] in 
let l_varnames_exogenous_variables = List.map (fun var -> match var with | Var(v, _) -> v) exogenous_variables in
let l_varnames_endogenous_variables = List.map (fun var -> match var with | Var(v, _) -> v) endogenous_variables in
";; activate model generation" :: 
"(set-option :produce-models true)" :: 
((l_exogenous_variables @
l_endogenous_variables @
l_equations) @
[ "(check-sat)" ;
"(get-value ( " ^ (List.fold_right (fun s1 s2 -> s1 ^ s2) l_varnames_exogenous_variables "") ^ (List.fold_right (fun s1 s2 -> s1 ^ s2) l_varnames_endogenous_variables "") ^ "))";
"(exit)" ])
;; 

let assignment_to_smt2 = fun var value ->
match var, value with
| Var(v, _), Const(c) -> "(assert (= " ^ v ^ " " ^ int_to_smt2(c) ^ "))"
;;

let situation_to_smt2 = fun m ->
match m with
| Situation(CausalModel(exogenous_variables, endogenous_variables, equations), context) -> 
let l_exogenous_variables = List.map variable_to_smt2 exogenous_variables in
let l_endogenous_variables = List.map variable_to_smt2 endogenous_variables in
let l_equations = VarMap.fold (fun var f lold -> (equation_to_smt2 var f) :: lold) equations [] in 
let l_varnames_exogenous_variables = List.map (fun var -> match var with | Var(v, _) -> v) exogenous_variables in
let l_varnames_endogenous_variables = List.map (fun var -> match var with | Var(v, _) -> v) endogenous_variables in
let l_assignments = VarMap.fold (fun var value lold -> (assignment_to_smt2 var value) :: lold) context [] in
";; activate model generation" :: 
"(set-option :produce-models true)" :: 
((l_exogenous_variables @
l_endogenous_variables @
l_equations @
l_assignments) @
[ "(check-sat)" ;
"(get-value ( " ^ (List.fold_right (fun s1 s2 -> s1 ^ " " ^ s2) l_varnames_exogenous_variables "") ^ (List.fold_right (fun s1 s2 -> s1 ^ " " ^ s2) l_varnames_endogenous_variables "") ^ "))";
"(exit)" ])
;; 

let main() =
  (* exogenous variables *)
  let i0 = Var("i0", Int) in
  let i1 = Var("i1", Int) in 
  let exogenous_vars = [ i0 ; i1 ] in
  (* endogenous variables *)
  let x0 = Var("x0", Int) in
  let y0 = Var("y0", Int) in
  let z0 = Var("z0", Int) in
  let z1 = Var("z1", Int) in
  let z2 = Var("z2", Int) in
  let z3 = Var("z3", Int) in
  let z4 = Var("z4", Int) in
  let z5 = Var("z5", Int) in
  let z6 = Var("z6", Int) in
  let z7 = Var("z7", Int) in
  let z8 = Var("z8", Int) in
  let l0 = Var("l0", Int) in
  let l1 = Var("l1", Int) in
  let l2 = Var("l2", Int) in
  let l3 = Var("l3", Int) in
  let l4 = Var("l4", Int) in
  let c0 = Var("c0", Boolean) in
  let c0p = Var("c0p", Boolean) in
  let c1 = Var("c1", Boolean) in
  let c1p = Var("c1p", Boolean) in
  let c2 = Var("c2", Boolean) in
  let c3 = Var("c3", Boolean) in
  let endogenous_vars = [ c0; c0p; c1; c1p; c2; c3; x0; y0; z0; z1; z2; z3; z4; z5; z6; z7; z8; l0; l1; l2; l3; l4 ] in 
  (* some constants *)
  let zero = Const(0) in
  let one = Const(1) in
  let two = Const(2) in
  let three = Const(3) in
  (* structural equations *)
  let equations = VarMap.empty in
  let equations = VarMap.add x0 (IntFunction(i0)) equations in
  let equations = VarMap.add y0 (IntFunction(i1)) equations in 
  let equations = VarMap.add c0 (BoolFunction(Relation(EQ, x0, zero))) equations in 
  let equations = VarMap.add c0p (BoolFunction(Relation(NEQ, x0, zero))) equations in 
  let equations = VarMap.add c1 (BoolFunction(Relation(EQ, y0, zero))) equations in
  let equations = VarMap.add c1p (BoolFunction(Relation(NEQ, y0, zero))) equations in
  let equations = VarMap.add c2 (BoolFunction(Relation(GT, z4, zero))) equations in
  let equations = VarMap.add c3 (BoolFunction(Relation(EQ, l4, zero))) equations in
  let equations = VarMap.add z0 (ConstIntFunction(zero)) equations in
  let equations = VarMap.add z1 (ConstIntFunction(one)) equations in
  let equations = VarMap.add z2 (ITE(And(c0, c1), z1, z0)) equations in
  let equations = VarMap.add z3 (IntFunction(y0)) equations in
  let equations = VarMap.add z4 (ITE(BoolVar(c1p), z3, z2)) equations in
  let equations = VarMap.add z5 (ConstIntFunction(two)) equations in
  let equations = VarMap.add z6 (ConstIntFunction(three)) equations in
  let equations = VarMap.add z7 (ITE(BoolVar(c2), z6, z4)) equations in
  let equations = VarMap.add z8 (ITE(BoolVar(c0p), z7, z5)) equations in
  let equations = VarMap.add l0 (ConstIntFunction(one)) equations in
  let equations = VarMap.add l1 (ConstIntFunction(zero)) equations in
  let equations = VarMap.add l2 (ConstIntFunction(zero)) equations in
  let equations = VarMap.add l3 (ITE(BoolVar(c2), l2, l0)) equations in
  let equations = VarMap.add l4 (ITE(Not(c0p), l3, l1)) equations in
  let model = CausalModel( exogenous_vars, endogenous_vars, equations) in
  let assignment = VarMap.empty in
  let assignment = VarMap.add i0 one assignment in
  let assignment = VarMap.add i1 (Const(-1)) assignment in 
  let situation = Situation(model, assignment) in 
  let situation2 = Situation((modify_model model l2 (ConstIntFunction(one))), assignment) in
  let l = situation_to_smt2(situation) in
  let oc = open_out "tmp.smt2" in
    List.iter (fun s -> Printf.fprintf oc "%s\n" s) l
  ;;

main();;
