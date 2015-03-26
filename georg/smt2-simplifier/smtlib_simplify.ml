open Smtlib_ast

module FormulaSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = formula
  end
);;


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
    * Assumes formulas are in negation normal form
*)
let rec is_unsat f g =
  match f, g with
  | LinearRelation (rel1, t1, c1), LinearRelation (rel2, t2, c2) ->
      t1 = t2 && (match rel1, rel2 with
      (* we are using integer arithmatic here 
       * x > 5 && x < 6 is unsat because no # between 5 and 6
       *)
      | LT, GT -> c1 + 1 >= c2
      | GT, LT -> c2 + 1 >= c1
      (* cases with one has n an EQ in it *)
      | LT, GEQ
      | LEQ, GT
      | EQ, GT
      | LT, EQ -> c1 <= c2
      | GT, LEQ
      | GEQ, LT
      | GT, EQ
      | EQ, LT -> c1 >= c2
      | LEQ, GEQ
      | EQ, GEQ
      | LEQ, EQ -> c1 < c2
      | GEQ, LEQ
      | EQ, LEQ
      | GEQ, EQ -> c1 > c2
      | EQ, EQ  -> c1 <> c2
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

let formula_size f = 
  let size = ref 0 in
  let rec aux f = 
    incr size;
    match f with 
    | True | False | UnsupportedFormula _ | Boolvar _ -> ()
    | Not f -> aux f
    | And fl -> List.iter aux fl
    | Or fl -> List.iter aux fl
    | Implication (f1,f2) -> aux f1;aux f2
    | ITE(f1,f2,f3) -> aux f1;aux f2; aux f3
    | Relation (_, t1,t2) -> term_aux t1; term_aux t2
    | LinearRelation (_,lhs,_) -> size := !size + List.length lhs
  and term_aux t = 
    incr size;
    match t with
    | Variable _ | Value _ | UnsupportedTerm _ -> ()
    | Sum tl -> List.iter term_aux tl
    | Mult tl -> List.iter term_aux tl
    | UMinus t -> term_aux t
  in
  aux f;
  !size





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
    let (_,result) = 
      List.fold_left (fun (i,a) e ->
	if (i = toAvoid) then (i+1,a)
	else (i+1, FormulaSet.add (fn e) a)) (0,set) lst
    in result
  in
  let isTrue trueHere f =
    match f with
    | Relation _ | LinearRelation _ ->
      FormulaSet.exists (is_unsat (mk_not f)) trueHere
    | _ -> FormulaSet.mem f trueHere
  in
  let isFalse trueHere f =
    match f with
    | Relation _ | LinearRelation _ ->
      FormulaSet.exists (is_unsat f) trueHere
    | _ -> FormulaSet.mem (mk_not f) trueHere
  in
  let rec aux trueHere  f = 
    if isTrue trueHere f then True
    else if isFalse trueHere f then False 
    else begin match f with

    (* in the context of an and, all other clauses in the and
     * are also true in the context of this one *)
      
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
    | _ -> f
    end
  in
  aux FormulaSet.empty f




let  simplify_constants  f  = 
  let remove_logical_consts lst = List.filter 
    (fun x -> match x with | True | False -> false | _ -> true) lst in
  let rec aux f = 

    match f with
    (*constants remain constant *)
    | True | False | UnsupportedFormula _ -> f
    (* DSN - this is a bit of a tricky thing, but we know that the flag vars must always be true *)
    | Boolvar _ -> True
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
    | Relation(EQ,a,b) when a = b -> True
    | Relation(LEQ,a,b) when a = b -> True
    | Relation(LT,a,b) when a = b -> False
    | Relation(GEQ,a,b) when a = b -> True
    | Relation(GT,a,b) when a = b -> False
    | Relation(NEQ,a,b) when a = b -> False
    | ITE(i,t,e) when t = e -> t

    (* evaluate according to the known value *)
    | Relation(EQ,Value(v1), Value(v2)) -> if v1 = v2 then True else False
    | Relation(LEQ,Value(v1), Value(v2)) -> if v1 <= v2 then True else False
    | Relation(LT,Value(v1), Value(v2)) -> if v1 < v2 then True else False
    | Relation(GEQ,Value(v1), Value(v2)) -> if v1 >= v2 then True else False
    | Relation(GT,Value(v1), Value(v2)) -> if v1 > v2 then True else False
    | Relation(NEQ,Value(v1), Value(v2)) -> if v1 <> v2 then True else False
    | Implication(False,_) -> True
    | Implication(_,True) -> True
    | Implication(True,x) -> x
    | Implication(x,False) -> mk_not x
    | Not(False) -> True
    | Not(True) -> False
    | ITE(True,t,e) -> t
    | ITE(False,t,e) -> e
    | ITE(i,t,False) -> And [aux i; aux t]
    | ITE(i,False,e) -> And [mk_not (aux i); aux e]
    | ITE(i,t,True) -> Implication(aux i,aux t)
    | ITE(i,True,e) -> Implication(mk_not (aux i),aux e)

    | And fl when List.exists (fun x -> x = False) fl -> False
    | Or fl when List.exists (fun x -> x = True) fl -> True

    (* Important that this happens after we have done the above test *)
    | And fl -> And(List.map aux (remove_logical_consts fl))
    | Or fl -> Or(List.map aux  (remove_logical_consts fl))

    (* recurse down the tree *)
    | Not f1 -> mk_not (aux f1)
    | Implication (f1,f2) -> Implication(aux f1,aux f2) 
    (* Don't simplify terms here *)
    | LinearRelation _ 
    | Relation _ -> f
    | ITE(f1,f2,f3) -> ITE(aux f1,aux f2,aux f3)
  in aux f



let normalize_formula f = 
  let flatten_nested_ands lst = 
    List.fold_right (function And gs -> fun acc -> gs @ acc | f -> fun acc -> f :: acc) lst []
  in
  let flatten_nested_ors lst = 
    List.fold_right (function Or gs -> fun acc -> gs @ acc | f -> fun acc -> f :: acc) lst []
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
    | _ -> f  
  in  
  aux f

    

let simplify_terms f = 
  let rec aux f = 
    match f with 
    (* base case: something with terms *)
    | Relation(op,t1,t2) -> Relation(op,normalize_term t1, normalize_term t2)

    (* recurse down the tree *)
    | True|False|UnsupportedFormula _ | Boolvar _ | LinearRelation _ -> f
    | Not f1 -> mk_not (aux f1)
    | And fl -> And (List.map aux fl)
    | Or  fl -> Or (List.map aux fl)
    | Implication (f1,f2) -> Implication(aux f1,aux f2) 
    | ITE(f1,f2,f3) -> ITE(aux f1,aux f2, aux f3)
  in
  aux f



(* we can strengthen this later *)
(* return Some reduced if reduction possible. None otherwise *)
let simplify_and_pair f1 f2 = 
  None

let simplify_or_pair f1 f2 = 
  None

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

let simplify_formula_2_new f = 
  let rec aux = function
    | And fs -> And(fold_pairs simplify_and_pair fs)
    | Or fs -> Or(fold_pairs simplify_and_pair fs)
    | Not f -> mk_not (aux f)
    | ITE (i,t,e) -> ITE(aux i, aux t, aux e)
    | Implication (f1, f2) -> Implication (aux f1, aux f2)
    | True | False | Relation _ | LinearRelation _ | UnsupportedFormula _ | Boolvar _ as f -> f
  in
  aux f

let simplify_formula_2 f =
  let rec aux f = 
    match f with
    (* Logical operators *)
    | And(fs) ->
      let f1 =
        begin match fs with 
	| Relation(GEQ, t1, Value c1) :: Relation(GT, t2, Value c2) :: gs
            when t1 = t2 && (c1 >= c2 + 1 || c2 + 1 >= c1) ->
          let c = max c1 (c2 + 1) in
          aux (And(Relation(GEQ, t1, Value c) :: gs))
	| Relation(GT, t1, Value c1) :: Relation(LEQ, t2, Value c2) :: gs
            when t1 = t2 && c1 + 1 = c2 ->
          aux (And (Relation(EQ, t1, Value c2) :: gs))
	| Relation(LT, t2, Value c2) :: Relation(GEQ, t1, Value c1) :: gs
            when t1 = t2 && c1 + 1 = c2 ->
          aux (And (Relation(EQ, t1, Value c1) :: gs))
	| Relation(GEQ, t1, Value c1) :: Relation(GEQ, t2, Value c2) :: gs
            when t1 = t2 && (c1 >= c2 || c2 >= c1) ->
          let c = max c1 c2 in
          aux (And(Relation(GEQ, t1, Value c) :: gs))
	| Relation(GEQ, t1, Value c1) :: Relation(EQ, t2, Value c2) :: gs
            when t1 = t2 && c1 <= c2 ->
          aux (And(Relation(EQ, t2, Value c2) :: gs))
	| Relation(GT, t1, Value c1) :: Relation(EQ, t2, Value c2) :: gs
            when t1 = t2 && c1 < c2 ->
          aux (And(Relation(EQ, t2, Value c2) :: gs))            
	| Relation(LEQ, t1, Value c1) :: Relation(LEQ, t2, Value c2) :: gs
            when t1 = t2 && (c1 <= c2 || c2 <= c1) ->
          let c = min c1 c2 in
          aux (And(Relation(LEQ, t1, Value c) :: gs))
	| Relation(LT, t1, t2) :: Relation(GEQ, t3, t4) :: gs
	| Relation(LT, t1, t2) :: Relation(GT, t3, t4) :: gs
	| Relation(LEQ, t1, t2) :: (Relation(LEQ, t3, t4) :: gs) 
	| Relation(LEQ, t1, t2) :: (Relation(GEQ, t4, t3) :: gs)
            when t1 = t4 && t2 = t3 ->
          aux (And (Relation(EQ, t1, t2) :: gs))
	| Relation(LEQ, t1, t2) :: (Relation(NEQ, t3, t4) :: gs)
            when t1 = t3 && t2 = t4 ->
          aux (And (Relation(LT, t1, t2) :: gs))
	| Relation(GEQ, t1, t2) :: (Relation(NEQ, t3, t4) :: gs)
            when t1 = t3 && t2 = t4 ->
          aux (And (Relation(GT, t1, t2) :: gs))
	| Relation(LEQ, t1, Value c1) :: Relation(LEQ, Value(0), Sum([ t2; Value c2 ])) :: gs
            when t1 = t2 && c1 = -1 * c2 -> 
          let phi = Relation(EQ,t1, Value c1) in
          aux (And (phi :: gs))
	| Relation(LEQ, Value(0), Sum([ t2; Value c2 ])) :: Relation(LEQ, t1, Value c1) :: gs
            when t1 = t2 && c1 = -1 * c2 -> 
          let phi = Relation(EQ,t1, Value c1) in
          aux (And(phi :: gs))
	| (Relation _ as g1) :: (Relation _ as g2) :: gs
            when is_unsat g1 g2 ->
          False
	| [ g ] -> aux g
	| [] -> True
	| g :: gs -> 
          let g1 = aux g in
          let
              h = aux (And(gs))
          in
          match g1, h with
          | False, _
          | _, False -> False
          | True, _ -> h
          | _, True -> g1
          | _, And(hs) -> And (g1 :: hs)
          | _, _ -> And [g1; h]
        end
      in
      (*print_endline "Before simplify: ";
        print_formula f ""; print_newline ();
        print_endline "After simplify: ";
        print_formula f1 ""; print_newline ();*)
      f1
    | LinearRelation _ -> failwith "need to handle this"
    | Or(fs) ->
      begin match fs with  
      | [ Relation(LEQ, Value c1, t1) ; Relation(LEQ, t2, Value c2) ]
	  when (t1 = t2 && c1 = c2 + 2) ->
        Relation(NEQ, t1, Value(c1 - 1)) (* overflow issues! *)
      | [ Relation(LEQ, t2, Value c2) ; Relation(LEQ, Value c1, t1) ]
	  when (t1 = t2 && c1 = c2 + 2) ->
        Relation(NEQ, t1, Value(c1 - 1)) (* overflow issues! *)
      | [Relation _ as f; Relation _ as g] when f = mk_not g -> True
      | [] -> False
      | [f] -> aux f
      | f :: gs ->
        let f1 = aux f in
        let h = aux (Or gs) in
        match f1, h with
        | True, _
        | _, True -> True
        | False, _ -> h
        | _, False -> f1
        | _, Or (hs) -> Or (f1 :: hs)
        | _, _ -> Or [f1; h]
      end




    (* recurse *)
    | Not f -> mk_not (aux f)
    | ITE (i,t,e) -> ITE(aux i, aux t, aux e)
    | Implication (f1, f2) -> Implication (aux f1, aux f2)
    | True | False | Relation _ | UnsupportedFormula _ | Boolvar _ -> f
  in
  aux f

let simplify_formula f = 
  let f = simplify_constants f in
  let f = normalize_formula f in
  let f = simplify_terms f in
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
