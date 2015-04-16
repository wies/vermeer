open Smtlib_util
open SmtSimpleAst
open SmtSimpleAstBuilder
open SmtSimpleNormalize

module FormulaSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = term
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
  | BoolConst c1, BoolConst c2 -> compare c1 c2
  | IntConst c1, IntConst c2 -> compare c1 c2
  | Ident (v1,s1), Ident(v2,s2) -> compare (v1,s1) (v2,s2)
  | LinearRelation (rel1, t1, c1), LinearRelation (rel2, t2, c2) ->
    compare (t1, c1, rel1) (t2, c2, rel2)        
  | App(o1,t1,s1),App (o2,t2,s2) ->
    let c = compare_lex t1 t2 in
    if c = 0 then compare (o1,s1) (o2,s2)
    else c
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
    | (Gt,a), (Lt,b) | (Lt,b), (Gt,a) -> a >= b 
      (* cases with one has n an Eq in it *)
    | (Lt,a), (Geq,b) | (Geq,b), (Lt,a)
    | (Leq,a), (Gt,b) | (Gt,b), (Leq,a)
    | (Eq,a), (Gt,b) | (Gt,b), (Eq,a)
    | (Lt,a), (Eq,b) | (Eq,b), (Lt,a) -> a <= b
    | (Leq,a), (Geq,b) | (Geq,b), (Leq,a)
    | (Eq,a), (Geq,b) | (Geq,b), (Eq,a)
    | (Leq,a), (Eq,b) | (Eq,b), (Leq,a) -> a < b
    | (Eq,a), (Eq,b)  -> a <> b
    | _, _ ->
      negate_rel rel1 = rel2 && c1 = c2)
  | BoolConst false, _
  | _, BoolConst false -> true
  | App(And,fs,_), g ->
    List.exists (fun f -> is_unsat f g) fs
  | App(Or,fs,_), g ->
    List.for_all (fun f -> is_unsat f g) fs
  | f, g -> mk_not f = g

let subsumes f g =
  let rec subs strengthen fs gs =
    match fs, gs with
    | [], _ -> true
    | _, [] -> false
    | (App(o1,t1,s1) as f)::fs, (App(o2,t2,s2) as g)::gs 
      when is_relation o1 && is_relation o2 ->
      if strengthen && is_unsat f (mk_not g) || not strengthen && is_unsat (mk_not f) g
      then subs strengthen fs (g::gs)
      else subs strengthen (f::fs) gs
    | (LinearRelation _ as f) :: fs, (LinearRelation _ as g) :: gs ->
      if strengthen && is_unsat f (mk_not g) || not strengthen && is_unsat (mk_not f) g
      then subs strengthen fs (g::gs)
      else subs strengthen (f::fs) gs
    | f :: fs, g :: gs ->
      if f = g then subs strengthen fs (g::gs)
      else subs strengthen (f::fs) gs
  in
  match f, g with
  | App(Or,fs,_), App(Or,gs,_) -> subs false fs gs
  | App(And,gs,_), App(And,fs,_) -> subs true fs gs
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
    | App(o,t,s) when is_relation o ->
      FormulaSet.exists (is_unsat f1) trueHere
    | LinearRelation _ ->
      FormulaSet.exists (is_unsat f1) trueHere
    | _ -> FormulaSet.mem f2 trueHere
  in
  let rec aux trueHere  f = 
    if check true trueHere f then begin 
      mk_boolConst true
    end
    else if check false trueHere f then begin
      mk_boolConst false
    end else begin match f with
    (* in the context of an And, all other clauses in the And
     * are also true in the context of this one (and dualy for Or) *)  
    | App(And,fl,_)-> 
      let fl = remove_duplicates true fl in
      mk_and (List.mapi (fun i e -> 
	let trueHere = add_all_but_i i (fun f -> f) fl trueHere in
	aux trueHere e) fl)
    | App(Or,fl,_) ->
      let fl = remove_duplicates false fl in
      mk_or (List.mapi (fun i e -> 
	let trueHere = add_all_but_i i mk_not fl trueHere in
	aux trueHere e) fl)
    | App(Not,[Ident _],_) as f -> f
    | App(Ite,_,_) | App(Impl,_,_) | App(Not,_,_)  -> 
      failwith ("expected formula in NNF: " ^ SmtSimpleFns.string_of_term f)
    | _ -> f
    end
  in
  aux FormulaSet.empty f


let simplify_constants  f  = 
  let rec aux = function
    (*constants remain constant *)
    | BoolConst _ | IntConst _ | Ident _ | LinearRelation _ as f -> f
    | App(Eq,[a;b],_) | App(Leq,[a;b],_)  | App(Geq,[a;b],_) 
	when a = b -> mk_boolConst true
    | App(Neq,[a;b],_) | App(Lt,[a;b],_)  | App(Gt,[a;b],_) 
	when a = b -> mk_boolConst false
    | App(And,fl,_) when List.mem (BoolConst false) fl -> mk_boolConst false
    | App(Or,fl,_) when List.mem (BoolConst true) fl -> mk_boolConst true
    | App(o,t,s) -> mk_app o (List.map aux t) 
  in aux f

(* we can strengthen this later *)
(* return Some reduced if reduction possible. None otherwise *)
let simplify_and_pair f1 f2 = 
  match f1,f2 with
  | LinearRelation(op1,t1,c1), LinearRelation(op2,t2,c2) when t1 = t2 -> begin
    match (op1,c1),(op2,c2) with
    | (Geq,a),(Gt,b) | (Gt,b),(Geq,a)
      when  (a >= Int64.succ b || Int64.succ b >= a) -> 
      let c = max a (Int64.succ b ) in
      Some (LinearRelation(Geq,t1,c))
    | (Gt,a),(Leq,b) | (Leq,b),(Gt,a)
      when Int64.succ a = b ->
      Some (LinearRelation(Eq,t1,b))
    | (Geq,a),(Lt,b) | (Lt, b),(Geq, a) 
      when Int64.succ a = b ->
      Some (LinearRelation(Eq,t1,a))
    | (Geq,a),(Geq,b) 
      when (a >= b || b >= a) ->
      let c = max a b in
      Some(LinearRelation(Geq, t1, c))
    | (Leq,a),(Leq,b)
      when (a >= b || b >= a) ->
      let c = min a b in
      Some(LinearRelation(Leq, t1, c))
    | (Geq,a),(Eq,b) | (Eq,b),(Geq,a)
      when a <= b -> Some(LinearRelation(Eq, t1, b))
    | (Gt,a),(Eq,b) | (Eq,b),(Gt,a)
      when a < b -> Some(LinearRelation(Eq, t1, b))
    | (Leq,a),(Neq,b) | (Neq,b),(Leq,a)
      when a = b ->
      Some(LinearRelation(Lt,t1,a))
    | (Geq,a),(Neq,b) | (Neq,b),(Geq,a)
      when a = b ->
      Some(LinearRelation(Gt,t1,a))
    | (Geq,a),(Leq,b) | (Leq,b),(Geq,a)
      when a = b->
      Some(LinearRelation(Eq,t1,a))
    | (Gt,a),(Lt,b) | (Lt,b),(Gt,a)
      when Int64.add a 2L = b ->
      Some(LinearRelation(Neq, t1, (Int64.succ a )))
    | _ -> None
  end
  | _ -> None

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
    | App(And,fs,_) -> mk_and (fold_pairs simplify_and_pair (List.map aux fs))
    | App(Or,fs,_) -> mk_or (fold_pairs simplify_or_pair (List.map aux fs))
    | IntConst _ | BoolConst _ | LinearRelation _ | Ident _ as f -> f
    | App(o,t,s) -> mk_app o (List.map aux t)
  in
  aux f

let simplify_formula f = 
  let f = simplify_constants f in
  let f = normalize_term f in
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
(*  (<= 0 (+ (- 1) x_11_1)) (<= 0 (+ (- 1) x_6_1)) (<= x_10_1 0) (<= x_11_1 1) *)

let test () = 
  let t1 = mk_rel Leq zero (mk_add [minus_one;mk_ident "x_11" IntSort]) in
  let t2 = mk_rel Leq (mk_ident "x_11" IntSort) one in
  let form = mk_and [t1;t2] in
  let lr = make_linear_relation Leq zero (mk_add [minus_one;mk_ident "x_11" IntSort]) in
  let beaut = beautify_formula form in
  (match beaut with
  | App(And,[LinearRelation _; LinearRelation _],s) -> print_endline "linear"
  | _ -> print_endline "non"
  );
print_endline (SmtSimpleFns.string_of_term beaut)
