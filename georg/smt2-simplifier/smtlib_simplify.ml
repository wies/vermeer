open Smtlib_util
open Smtlib_ast
open Smtlib_normalize
open Smtlib_ast_print

module FormulaSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = formula
  end)


let rec compare_form f g =
  let rec compare_lex fs gs =
    match fs, gs with
    | f :: fs1, g :: gs1 ->
      let c = compare_form f g in
      if c = 0
      then compare_lex fs1 gs1
      else c
    | [], _ :: _ -> -1
    | _ :: _, [] -> 1
    | _, _ -> 0
  in
  match (f, g) with
  | Relation (rel1, t1, t2), Relation (rel2, t3, t4) ->
    compare (t1, t2, rel1) (t3, t4, rel2)
  | LinearRelation (rel1, t1, c1), LinearRelation (rel2, t2, c2) ->
    compare (t1, c1, rel1) (t2, c2, rel2)        
  | Not f, Not g ->
    compare_form f g
  | And fs, And gs ->
    compare_lex fs gs
  | Or fs, Or gs ->
    compare_lex fs gs
  | Implication (f1, f2), Implication (f3, f4) ->
    compare_lex [f1; f2] [f3; f4]
  | ITE (f1, f2, f3), ITE (f4, f5, f6) ->
    compare_lex [f1; f2; f3] [f4; f5; f6]
  | f, g -> compare f g

(** Check whether conjunction of the two formulas is unsat.
 ** Assumes formulas are in negation normal form.
 *)
let rec is_unsat f g =
  match f, g with
  | LinearRelation (rel1, t1, c1), LinearRelation (rel2, t2, c2) ->
    t1 = t2 && (match (rel1,c1), (rel2,c2) with
      (* we are using integer arithmatic here 
       * x > 5 && x < 6 is unsat because no # between 5 and 6
       *)
    | (GT,a), (LT,b) | (LT,b), (GT,a) -> a >= b 
      (* cases with one has n an EQ in it *)
    | (LT,a), (GEQ,b) | (GEQ,b), (LT,a)
    | (LEQ,a), (GT,b) | (GT,b), (LEQ,a)
    | (EQ,a), (GT,b) | (GT,b), (EQ,a)
    | (LT,a), (EQ,b) | (EQ,b), (LT,a) -> a <= b
    | (LEQ,a), (GEQ,b) | (GEQ,b), (LEQ,a)
    | (EQ,a), (GEQ,b) | (GEQ,b), (EQ,a)
    | (LEQ,a), (EQ,b) | (EQ,b), (LEQ,a) -> a < b
    | (EQ,a), (EQ,b)  -> a <> b
    | _, _ ->
      negate_rel rel1 = rel2 && c1 = c2)
  | False, _
  | _, False -> true
  | And fs, g ->
    List.exists (fun f -> is_unsat f g) fs
  | Or fs, g ->
    List.for_all (fun f -> is_unsat f g) fs
  | f, g -> mk_not f = g

let subsumes f g =
  let rec subs strengthen fs gs =
    match fs, gs with
    | [], _ -> true
    | _, [] -> false
    | (Relation _ as f) :: fs, (Relation _ as g) :: gs
    | (LinearRelation _ as f) :: fs, (LinearRelation _ as g) :: gs ->
      if strengthen && is_unsat f (mk_not g) || not strengthen && is_unsat (mk_not f) g
      then subs strengthen fs (g::gs)
      else subs strengthen (f::fs) gs
    | f :: fs, g :: gs ->
      if f = g then subs strengthen fs (g::gs)
      else subs strengthen (f::fs) gs
  in
  match f, g with
  | Or fs, Or gs -> subs false fs gs
  | And gs, And fs -> subs true fs gs
  | f, g -> subs true [f] [g]
    
(* remove duplicates from a list *)
let remove_duplicates strengthen fs = 
  let rec uniq = function
    | [] -> []
    | e1 :: e2 :: tl when subsumes e1 e2 ->
      if strengthen
      then e1 :: uniq tl
      else e2 :: uniq tl
    | e1 :: e2 :: tl when subsumes e2 e1 ->
      if strengthen
      then e2 :: uniq tl
      else e1 :: uniq tl
    | hd :: tl -> hd :: uniq tl
  in
  let sorted = List.sort compare_form fs in
  uniq sorted    

(* DSN there is probably a better way to do this.
 * What I'm trying to do here is to take advantage of the fact that 
 * A && (A || B), can be simplified to A && (True || B)
 * So, maintain a set of things that are known to be contextually "true"
 * I keep two sets, one which is things which are true here, and one which is 
 * only true for the children.
 * This also holds for implications.
 * A ==> (A && B)  ~~~ A ===> B
 *)

let propagate_truth_context f =
  let add_all_but_i toAvoid fn lst set = 
    let _, result = 
      List.fold_left (fun (i, a) e ->
	if i = toAvoid then (i+1,a)
	else (i+1, FormulaSet.add (fn e) a)) (0, set) lst
    in result
  in
  let check truth trueHere f =
    let f1, f2 = if truth then mk_not f, f else f, mk_not f in
    match f with
    | Relation _ | LinearRelation _ ->
      FormulaSet.exists (is_unsat f1) trueHere
    | _ -> FormulaSet.mem f2 trueHere
  in
  let rec aux trueHere  f = 
    if check true trueHere f then begin
      True
    end
    else if check false trueHere f then begin
      False 
    end else begin match f with
    (* in the context of an And, all other clauses in the And
     * are also true in the context of this one (and dualy for Or) *)  
    | And fl -> 
      let fl = remove_duplicates true fl in
      And (List.mapi (fun i e -> 
	let trueHere = add_all_but_i i (fun f -> f) fl trueHere in
	aux trueHere e) fl)
    | Or fl ->
      let fl = remove_duplicates false fl in
      Or (List.mapi (fun i e -> 
	let trueHere = add_all_but_i i mk_not fl trueHere in
	aux trueHere e) fl)
    | Not Boolvar _ as f -> f
    | ITE _ | Implication _ | Not _ -> failwith "expected formula in NNF"
    | _ -> f
    end
  in
  aux FormulaSet.empty f


let  simplify_constants  f  = 
  let remove_logical_consts lst =
    List.filter (function True | False -> false | _ -> true) lst
  in
  let rec aux f = 
    match f with
    (*constants remain constant *)
    | True | False | UnsupportedFormula _ -> f
    (* DSN - this is a bit of a tricky thing, but we know that the flag vars must always be true *)
    (* | Boolvar _ -> True *)
    | LinearRelation (EQ, [], 0) 
    | LinearRelation (LEQ, [], 0)
    | LinearRelation (GEQ, [], 0) -> True
    | LinearRelation (EQ, [], _)
    | LinearRelation (NEQ, [], 0) -> False
    | LinearRelation (LEQ, [], v)
    | LinearRelation (LT, [], v) -> if v > 0 then True else False
    | LinearRelation (GEQ, [], v)
    | LinearRelation (GT, [], v) -> if v < 0 then True else False

    (* We can special case a = a *)
    | Relation(EQ,a,b) 
    | Relation(LEQ,a,b)
    | Relation(GEQ,a,b) 
	when a = b -> True
    | Relation(LT,a,b)
    | Relation(GT,a,b)
    | Relation(NEQ,a,b) 
	when a = b -> False

    | And fl when List.mem False fl -> False
    | Or fl when List.mem True fl -> True

    (* Important that this happens after we have done the above test *)
    | And fl -> And(List.map aux (remove_logical_consts fl))
    | Or fl -> Or(List.map aux  (remove_logical_consts fl))

    (* Don't simplify terms here *)
    | Not Boolvar _ as f -> f
    | ITE _ | Implication _ | Not _ -> failwith "expected formula in NNF"   
    | _ -> f
  in aux f



let normalize_formula f = 
  let flatten_nested_ands lst = 
    List.fold_left (fun acc -> function And gs -> gs @ acc | f -> f :: acc) [] lst
  in
  let flatten_nested_ors lst = 
    List.fold_left (fun acc -> function Or gs -> gs @ acc | f -> f :: acc) [] lst
  in
  let rec aux f = 
    match f with 
    (* Structural normalization *)
    | And []  -> True
    | And [f1] -> aux f1
    | And lst -> And (List.map aux (remove_duplicates true (flatten_nested_ands lst)))
    | Or []  -> False
    | Or [f1] -> aux f1
    | Or lst -> Or (List.map aux (remove_duplicates false (flatten_nested_ors lst)))
    | Relation (op,lhs,rhs) -> normalize_relation op lhs rhs
    | Not Boolvar _ as f -> f
    | ITE _ | Implication _ | Not _ -> failwith "expected formula in NNF"
    | _ -> f  
  in  
  aux f


let simplify_and_pair_2 f1 f2 = 
  match f1,f2 with
  | LinearRelation(op1,t1,c1), LinearRelation(op2,t2,c2) when t1 = t2 -> begin
    match (op1,c1),(op2,c2) with
    | (GEQ,a),(GT,b) | (GT,b),(GEQ,a)
      when  (a >= b + 1 || b + 1 >= a) -> 
      let c = max a (b + 1) in
      Some (LinearRelation(GEQ,t1,c))
    | (GT,a),(LEQ,b) | (LEQ,b),(GT,a)
      when a + 1 = b ->
      Some (LinearRelation(EQ,t1,b))
    | (GEQ,a),(LT,b) | (LT, b),(GEQ, a) 
      when a + 1 = b ->
      Some (LinearRelation(EQ,t1,a))
    | (GEQ,a),(GEQ,b) 
      when (a >= b || b >= a) ->
      let c = max a b in
      Some(LinearRelation(GEQ, t1, c))
    | (LEQ,a),(LEQ,b)
      when (a >= b || b >= a) ->
      let c = min a b in
      Some(LinearRelation(LEQ, t1, c))
    | (GEQ,a),(EQ,b) | (EQ,b),(GEQ,a)
      when a <= b -> Some(LinearRelation(EQ, t1, b))
    | (GT,a),(EQ,b) | (EQ,b),(GT,a)
      when a < b -> Some(LinearRelation(EQ, t1, b))
    | (LEQ,a),(NEQ,b) | (NEQ,b),(LEQ,a)
      when a = b ->
      Some(LinearRelation(LT,t1,a))
    | (GEQ,a),(NEQ,b) | (NEQ,b),(GEQ,a)
      when a = b ->
      Some(LinearRelation(GT,t1,a))
    | (GEQ,a),(LEQ,b) | (LEQ,b),(GEQ,a)
      when a = b->
      Some(LinearRelation(EQ,t1,a))
    | (GT,a),(LT,b) | (LT,b),(GT,a)
      when a + 2 = b ->
      Some(LinearRelation(NEQ, t1, (a + 1)))
    | _ -> None
  end
  | _ -> None

(* we can strengthen this later *)
(* return Some reduced if reduction possible. None otherwise *)
let simplify_and_pair f1 f2 = 
  simplify_and_pair_2 f1 f2
(*
  match f1,f2 with
  | LinearRelation(GEQ, t1,  c1) , LinearRelation(GT, t2,  c2) 
    when t1 = t2 && (c1 >= c2 + 1 || c2 + 1 >= c1) ->
    let c = max c1 (c2 + 1) in
    Some (LinearRelation(GEQ,t1,c))
  | LinearRelation(GT, t1,  c1) , LinearRelation(LEQ, t2,  c2)
    when t1 = t2 && c1 + 1 = c2 ->
    Some (LinearRelation(EQ, t1,  c2))
  | LinearRelation(LT, t2,  c2) , LinearRelation(GEQ, t1,  c1) 
    when t1 = t2 && c1 + 1 = c2 ->
    Some (LinearRelation(EQ, t1,  c1))
  | LinearRelation(GEQ, t1,  c1) , LinearRelation(GEQ, t2,  c2) 
    when t1 = t2 && (c1 >= c2 || c2 >= c1) ->
    let c = max c1 c2 in
    Some(LinearRelation(GEQ, t1, c))
  | LinearRelation(GEQ, t1, c1) , LinearRelation(EQ, t2, c2)
    when t1 = t2 && c1 <= c2 ->
    Some(LinearRelation(EQ, t2, c2))
  | LinearRelation(GT, t1, c1) , LinearRelation(EQ, t2, c2) 
    when t1 = t2 && c1 < c2 ->
    Some (LinearRelation(EQ, t2, c2))
  | LinearRelation(LEQ, t1, c1) , LinearRelation(LEQ, t2, c2) 
    when t1 = t2 && (c1 <= c2 || c2 <= c1) ->
    let c = min c1 c2 in
    Some(LinearRelation(LEQ, t1,  c))
  | LinearRelation(LEQ, t1, t2) , LinearRelation(NEQ, t3, t4)
    when t1 = t3 && t2 = t4 ->
    Some (LinearRelation(LT, t1, t2))
  | LinearRelation(GEQ, t1, t2) , LinearRelation(NEQ, t3, t4)
    when t1 = t3 && t2 = t4 ->
    Some(LinearRelation(GT, t1, t2))
      
  | LinearRelation(LEQ,t1,c1), LinearRelation(GEQ, t2,c2)
  | LinearRelation(GEQ,t1,c1), LinearRelation(LEQ, t2,c2) 
    when t1 = t2 && c1 = c2 ->
    Some (LinearRelation(EQ, t1, c1))

  (* DSN this does not feel exhausetive.  
   * Perhaps some way to take advantage of the negate_rel fn*)
  | _ ->
    None
*)

let simplify_or_pair f1 f2 = Opt.map mk_not (simplify_and_pair (mk_not f1) (mk_not f2))

let fold_pairs fn lst = 
  let rec aux = function  
    | [] -> []
    | [x] -> [x]
    | t1::t2::rest -> begin
      match fn t1 t2 with
      | Some r -> aux (r::rest)
      | None -> t1 :: (aux (t2::rest))
    end    
  in aux lst

let simplify_formula_2 f = 
  let rec aux = function
    | And fs -> And(fold_pairs simplify_and_pair (List.map aux fs))
    | Or fs -> Or(fold_pairs simplify_or_pair (List.map aux fs))
    | True | False | Relation _ | LinearRelation _ | UnsupportedFormula _ | Boolvar _ as f -> f
    | Not Boolvar _ as f -> f
    | ITE _ | Implication _ | Not _ -> failwith "expected formula in NNF"
  in
  aux f

let simplify_formula f = 
  let f = simplify_constants f in
  let f = normalize_formula f in
  let f = propagate_truth_context f in
  let f = simplify_formula_2 f in
  f

let beautify_formula f = run_fixpt simplify_formula (nnf f)


(*
  In the else branch of x_6_6 = 5

  IF (
  (x_6_6 + -4) <= 0
  ) THEN (
  0 <= (x_6_6 + -5)
  ) ELSE (
  OR (
  (x_6_6 + -5) <= 0
  x_6_6 <= 5
  )
  )
*)

let test () =
  let x = Variable "x" in
  let zero = Value 0 in
  let f = 
    And [
      Not (Relation (EQ,x,Value 5));
      ITE(
	Relation(LEQ, Sum[x;Value (-4)], zero),
	Relation(LEQ, zero, Sum[x; Value (-5)]),
	Or [
	  Relation(LEQ,Sum[x;Value (-5)],zero);
	  Relation(LEQ, x, Value 5)])] in
  let bf = beautify_formula f  in
  print_formula bf ""
