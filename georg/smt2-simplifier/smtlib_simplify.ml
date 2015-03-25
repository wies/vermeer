open Smtlib_ast

module FormulaSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = formula
  end
);;

let rec run_fixpt fn term = 
  let newTerm = fn term in
  if newTerm = term 
  then term 
  else run_fixpt fn newTerm

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
    let c13 = compare t1 t3 in
    if c13 = 0 then
      let c24 = compare t2 t4 in
      if c24 = 0
      then compare rel1 rel2
      else c24
    else c13
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
  | Relation (rel1, t11, t12), Relation (rel2, t21, t22) ->
    (*if t11 = t21 && t12 = t22 then 
      (match rel1,rel2 with
      (* equality *)
      | EQ,LT | EQ,GT | EQ,NEQ
      | LT,EQ | GT,EQ | NEQ,EQ -> true
      | LEQ,GT | GEQ,LT | LT,GT | GT,LT -> true
      | _ -> false
      )
      else if*) t11 = t21 &&
  (match rel1, t12, rel2, t22 with
      (* Values *)
      (* we are using integer arithmatic here 
       * x > 5 && x < 6 is unsat because no # between 5 and 6
       *)
  | LT, Value c1, GT, Value c2
  | GT, Value c2, LT, Value c1 
    -> 
    c1+1 >= c2
      (* cases with one has n an EQ in it *)
  | LT, Value c1, GEQ, Value c2
  | LEQ, Value c1, GT, Value c2
  | EQ, Value c1, GT, Value c2
  | LT, Value c1, EQ, Value c2
    -> c1 <= c2
  | GT, Value c1, LEQ, Value c2
  | GEQ, Value c1, LT, Value c2
  | GT, Value c1, EQ, Value c2
  | EQ, Value c1, LT, Value c2
    -> c1 >= c2
  | LEQ, Value c1, GEQ, Value c2
  | EQ, Value c1, GEQ, Value c2
  | LEQ, Value c1, EQ, Value c2
    -> c1 < c2
  | GEQ, Value c1, LEQ, Value c2
  | EQ, Value c1, LEQ, Value c2
  | GEQ, Value c1, EQ, Value c2
    -> c1 > c2
  | EQ, Value c1, EQ, Value c2
    -> c1 <> c2
  | _, Variable _, _, Variable _ ->
    is_unsat (Relation (rel1, Sum [t11; UMinus t12], Value 0))
      (Relation (rel2, Sum [t21; UMinus t22], Value 0))
  | _, Variable _, _, Sum [(Variable _ as t); Value c] ->
    is_unsat (Relation (rel1, Sum [t11; UMinus t12], Value 0))
      (Relation (rel2, Sum [t21; UMinus t], Value c))
  | _, _, _, _ ->
    negate_rel rel1 = rel2 && t12 = t22)
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
    | (Relation _ as f) :: fs, (Relation _ as g) :: gs ->
      if strengthen && is_unsat f (mk_not g) ||
	not strengthen && is_unsat (mk_not f) g
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


let sort_vars = List.sort 
  (fun x y -> match x,y with 
  | Variable x, Variable y -> compare x y
  | _ -> failwith "not a var???")

(*Could make this slightly faster but who cares *)
let split_term_list tl = 
  let (vars,rest) = List.partition 
    (fun x -> match x with | Variable _ -> true | _ -> false) tl in
  let vars = sort_vars vars in
  let (vals,rest) = List.partition
    (fun x -> match x with  Value _ -> true | _ -> false) rest in
  let (sums,rest)  = List.partition
    (fun x -> match x with  Sum _ -> true | _ -> false) rest in
  let (mults,rest)  = List.partition
    (fun x -> match x with  Mult _ -> true | _ -> false) rest in
  (vars,vals,sums,mults,rest)

let split_vars_vals tl : (term list * term list * term list)= 
  let (vars,rest) = List.partition 
    (fun x -> match x with | Variable _ | UMinus (Variable _) -> true | _ -> false) tl in
  let vars = sort_vars vars in
  let (vals,rest) = List.partition
    (fun x -> match x with  Value _ -> true | _ -> false) rest in
  (vars,vals,rest)



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
    | Relation _ ->
      FormulaSet.exists (is_unsat (mk_not f)) trueHere
    | _ -> FormulaSet.mem f trueHere
  in
  let isFalse trueHere f =
    match f with
    | Relation _ ->
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
    (*Or (List.map (aux trueHere) fl)*)
    | Implication (f1,f2) -> 
      (* DSN we could go deeper by saying AND(a,b,c) -> d allows us to state 
       * any of a,b,c *)
      let lhs = aux trueHere  f1 in
      let rhs = aux (FormulaSet.add lhs trueHere)  f2 in
      Implication(lhs,rhs) 
	
    | ITE(i,t,e) -> 
      let i = aux trueHere  i in
      let t = aux (FormulaSet.add i trueHere) t in
      (* TODO there ought to be a better way to handle the else case *)
      let e = aux (FormulaSet.add (mk_not i) trueHere)  e in
      ITE(i,t,e)
	
    (* recurse into the tree *)
    | Not f1 -> mk_not (aux trueHere f1)
    | True|False|UnsupportedFormula _ | Relation _ | Boolvar _ | LinearRelation _ -> f
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
    | LinearRelation _ -> failwith "need to handle this"

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
    | Relation _ -> f
    | ITE(f1,f2,f3) -> ITE(aux f1,aux f2,aux f3)
  in aux f



let normalize_formula f = 
  let flatten_nested_ands lst = 
    let fs1, fs2 =  List.partition 
      (fun (f) -> match f with | And(_) -> false | _ -> true) lst in
    let fs2_extracted =
      List.map (fun (f) -> match f with | And(gs) -> gs | _ -> []) fs2
    in
    List.append fs1 (List.concat fs2_extracted)
  in
  let flatten_nested_ors lst = 
    let fs1, fs2 =  List.partition 
      (fun (f) -> match f with | Or(_) -> false | _ -> true) lst in
    let fs2_extracted =
      List.map (fun (f) -> match f with | Or(gs) -> gs | _ -> []) fs2
    in
    List.append fs1 (List.concat fs2_extracted)
  in

  let rec aux f = 
    (* Normalize relations.  We want the precendence 
     * variable (in sorted order), 
     * non-variable expression,
     * value
     *)
    
    match f with 
    (* For two vars, put them in lex order *)
    | Relation(oldOp, Variable x, Variable y) ->
      if x < y then f else Relation(invert_rel oldOp,Variable y, Variable x)
	
    (* move the variable to the left *)
    | Relation(op,y,Variable x) -> Relation(invert_rel op,Variable(x),y)

    (* move the value to the right *)
    | Relation(op,Value v,x) -> Relation(invert_rel op,x,Value v)

    (* Deeper look into relations - move constants out of sums *)
    (* t1 + v1 = v2 ~~~ t1 = v2 - v1*)
    (* DSN TODO - should be able to make this more general *)
    | Relation(op,Sum([ t1 ; Value(v1) ]), Value(v2)) -> 
      Relation(op,t1, Value(v2 - v1))

    (*convert  (x_156_1 +  (x_157_1 * -1)) <= 0 to x_156_1 <= x_157_1 *)
    | Relation(op,
	       Sum[Variable x; Mult[Variable y; Value v1]], 
	       Value v2) -> 
      Relation(op,
	       Variable x,
	       Sum[Mult[Variable y; Value (v1 * (-1))];Value v2])

    (* convert (x_47_1 + (1 + (x_48_1 * -1))) <= 0 to x_47_1 <= x_48_1 - 1 *) 
    | Relation(op,
	       Sum[Variable x; Value v0; Mult[Variable y; Value v1]], 
	       Value v2) ->
      Relation(op,
	       Variable x, 
	       Sum[Mult [Sum[Value v0; Mult[Variable y; Value v1]]; Value (-1)];
		   Value v2]) 
	
    (* x <= y - 1 ~~~ x < y *)
    (* TODO generalize *)
    | Relation(LEQ, Variable(v1), Sum([ Variable(v2); Value(-1) ])) ->
      Relation(LT, Variable(v1), Variable(v2))
    | Relation(GT, Variable(v1), Sum([ Variable(v2); Value(-1) ])) ->
      Relation(GEQ, Variable(v1), Variable(v2))

    (* (x_17_3 * -1) <= 0 *)
    | Relation(op, Mult [Variable v1; Value(-1)], Value v) ->
      Relation(invert_rel op, Variable v1, Value (v * -1))
	

    (* Structural normalization *)
    | Not Not f1 -> aux f1
    | And []  -> True
    | And [f1] -> aux f1
    | And lst -> And(List.map aux (remove_duplicates true (flatten_nested_ands lst)))
    | Or []  -> False
    | Or [f1] -> aux f1
    | Or lst -> Or(List.map aux (remove_duplicates false (flatten_nested_ors lst)))

    (* recurse down the tree *)
    | LinearRelation _ -> failwith "need to handle this"
    | Relation _ -> f
    | Not f1 -> mk_not (aux f1)
    | Implication (f1,f2) -> 
      Implication(aux f1,aux f2) 
    | ITE(f1,f2,f3) -> 
      ITE(aux f1,aux f2, aux f3)
    | True|False|UnsupportedFormula _ | Boolvar _ -> f  
  in  
  aux f

let rec simplify_term t = 
  let flatten_nested_mults lst = 
    let fs1, fs2 =  List.partition 
      (fun (f) -> match f with | Mult(_) -> false | _ -> true) lst in
    let fs2_extracted =
      List.map (fun (f) -> match f with | Mult(gs) -> gs | _ -> []) fs2
    in
    List.append fs1 (List.concat fs2_extracted)
  in
  let flatten_nested_sums lst = 
    let fs1, fs2 =  List.partition 
      (fun (f) -> match f with | Sum(_) -> false | _ -> true) lst in
    let fs2_extracted =
      List.map (fun (f) -> match f with | Sum(gs) -> gs | _ -> []) fs2
    in
    List.append fs1 (List.concat fs2_extracted)
  in
  match t with
    (* Handle constants *)
  | UMinus (Value c) -> Value (-c)
  | UMinus (Sum ts) ->
    simplify_term (Sum (List.map (function t -> UMinus t) ts))
  | UMinus (Mult ts) ->
    simplify_term (Mult (Value(-1) :: ts))
  | Sum [x] -> x
  | Mult [x] -> x
    (* do we want to distribute mults across sums ??? *)
    
    (* Normalize so that sums and mults always have the variable(s) on the left *)
  | Sum(lst) -> 
    let lst = List.map simplify_term lst in
    let (vars,vals,rest) = split_vars_vals lst in
    let vals = simplify_vals vals (+) 0 in
    let rest = flatten_nested_sums rest in
    Sum(vars @ vals  @ rest)
  | Mult(lst) -> begin
    let lst = List.map simplify_term lst in
    let (vars,vals,rest) = split_vars_vals lst in
    let vals = simplify_vals vals ( * ) 1 in
    let rest = flatten_nested_mults rest in
      (* distribute multiplication inside addition
       * this opens up more normalization oppertunities *)
    match vars,vals,rest with
    | [],[Value v],[Sum l] -> Sum (List.map (fun x -> Mult [Value v; x]) l)
    | _ -> Mult(vars @ vals  @ rest)
  end
  | Variable _ | Value _ | UnsupportedTerm _ | UMinus _ -> t
and simplify_vals vals op identity =
  let v = List.fold_left 
    (fun a x -> match x with 
    | Value v -> op a v
    | _ -> failwith "should be only values here"
    ) identity vals in
    (* If + simplified to 0, then no need to add it.  Same for * and 1 *) 
  if v = identity then []
  else [Value(v)]
    

let simplify_terms f = 

  let rec aux f = 
    match f with 
    (* base case: something with terms *)
    | Relation(op,t1,t2) -> Relation(op,simplify_term t1, simplify_term t2)

    (* recurse down the tree *)
    | True|False|UnsupportedFormula _ | Boolvar _ | LinearRelation _ -> f
    | Not f1 -> mk_not (aux f1)
    | And fl -> And (List.map aux fl)
    | Or  fl -> Or (List.map aux fl)
    | Implication (f1,f2) -> Implication(aux f1,aux f2) 
    | ITE(f1,f2,f3) -> ITE(aux f1,aux f2, aux f3)
  in
  aux f

let normalize_relation op lhs rhs = 
  (*first, move everything interresting to the lhs *)
  (* RHS is implictly 0 now *)
  let newLHS = Sum[lhs;UMinus rhs] in
  let newLHS = run_fixpt simplify_terms newLHS in
  match newLHS with 
  | Sum tl -> 
  | Variable v -> 
  | Mult tl ->
  | Uminus (Variable v) ->
  |  _ -> Relation(op,lhs,rhs)
    lhs
  | _ -> failwith "wtf"



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

let beautify_formula f =
  let rec loop f =
    let f_simple = simplify_formula f in
    if f = f_simple then
      f_simple
    else
      loop f_simple
  in loop (nnf f)

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
