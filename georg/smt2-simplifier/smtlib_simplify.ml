open Smtlib_ast

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

    
let formula_size f = 
  let size = ref 0 in
  let rec aux f = 
    incr size;
    match f with 
    | True | False | UnsupportedFormula _ -> ()
    | Not f -> aux f
    | And fl -> List.iter aux fl
    | Or fl -> List.iter aux fl
    | Implication (f1,f2) -> aux f1;aux f2
    | ITE(f1,f2,f3) -> aux f1;aux f2; aux f3
    | Relation (_, t1,t2) -> term_aux t1; term_aux t2
  and term_aux t = 
    incr size;
    match t with
    | Variable _ | Value _ | UnsupportedTerm _ -> ()
    | Sum tl -> List.iter term_aux tl
    | Mult tl -> List.iter term_aux tl
  in
  aux f;
  !size

module FormulaSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = formula
  end
);;

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
    (fun x -> match x with | Variable _ -> true | _ -> false) tl in
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
  let isTrue trueHere f =  FormulaSet.mem f trueHere  in
  let isFalse trueHere f = 
    match f with 
    | Not f -> FormulaSet.mem f trueHere
    | _ -> FormulaSet.mem (Not f) trueHere in
  let rec aux trueHere trueChildren f = 
    if isTrue trueHere f then True
    else if isFalse trueHere f then False 
    else 
      let trueHere = FormulaSet.union trueHere trueChildren in
      let trueChildren = FormulaSet.empty in
      
      match f with
      | And fl -> 
	let trueChildren = 
	  List.fold_left (fun a e -> FormulaSet.add e a) FormulaSet.empty fl in
	And (List.map (aux trueHere trueChildren) fl)
	  
      | Implication (f1,f2) -> 
	(* DSN we could go deeper by saying AND(a,b,c) -> d allows us to state 
	 * any of a,b,c *)
	let lhs = aux trueHere trueChildren f1 in
	let rhs = aux (FormulaSet.add lhs trueHere) trueChildren f2 in
	Implication(lhs,rhs) 

      | ITE(i,t,e) -> 
	let i = aux trueHere trueChildren i in
	let t = aux (FormulaSet.add i trueHere) trueChildren t in
	(* TODO there ought to be a better way to handle the else case *)
	let e = aux (FormulaSet.add (Not i) trueHere) trueChildren e in
	ITE(i,t,e)

      (* recurse into the tree *)
      | Relation _ -> f
      | Not f1 -> Not (aux trueHere trueChildren f1)
      | Or  fl -> Or (List.map (aux trueHere trueChildren) fl)
      | True|False|UnsupportedFormula _ -> f
  in
  aux FormulaSet.empty FormulaSet.empty f


let  simplify_constants  f  = 
  let remove_logical_consts lst = List.filter 
    (fun x -> match x with | True | False -> false | _ -> true) lst in
  let rec aux f = 

    match f with
    (*constants remain constant *)
    | True | False | UnsupportedFormula _ -> f
      
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
    | Implication(x,False) -> Not x
    | Not(False) -> True
    | Not(True) -> False
    | ITE(True,t,e) -> t
    | ITE(False,t,e) -> e
    | ITE(i,t,False) -> And [aux i; aux t]
    | ITE(i,False,e) -> And [Not (aux i); aux e]
    | ITE(i,t,True) -> Implication(aux i,aux t)
    | ITE(i,True,e) -> Implication(Not (aux i),aux e)

    | And fl when List.exists (fun x -> x = False) fl -> False
    | Or fl when List.exists (fun x -> x = True) fl -> True

    (* Important that this happens after we have done the above test *)
    | And fl -> And(List.map aux (remove_logical_consts fl))
    | Or fl -> Or(List.map aux  (remove_logical_consts fl))

    (* recurse down the tree *)
    | Not f1 -> Not (aux f1)
    | Implication (f1,f2) -> Implication(aux f1,aux f2) 
    (* Don't simplify terms here *)
    | Relation _ -> f
    | ITE(f1,f2,f3) -> ITE(aux f1,aux f2,aux f3)
  in aux f

let normalize_formula f = 
  let op_after_swap oldop = match oldop with
    | EQ  -> EQ 
    | LEQ -> GEQ
    | LT  -> GT
    | GEQ -> LEQ
    | GT  -> LT
    | NEQ -> NEQ
  in
  let remove_duplicates fs = 
    let rec uniq = function
      | [] -> []
      | e1 :: e2 :: tl when e1 = e2 -> e1 :: uniq tl
      | hd :: tl -> hd :: uniq tl
    in
    let sorted = List.sort compare_form fs in
    uniq sorted
  in
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
      if x < y then f else Relation(op_after_swap oldOp,Variable y, Variable x)
	
    (* move the variable to the left *)
    | Relation(op,y,Variable x) -> Relation(op_after_swap op,Variable(x),y)

    (* move the value to the right *)
    | Relation(op,Value v,x) -> Relation(op_after_swap op,x,Value v)

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

	

    (* Structural normalization *)
    | Not Not f1 -> aux f1
    | And []  -> True
    | And [f1] -> aux f1
    | And lst -> And(List.map aux (remove_duplicates (flatten_nested_ands lst)))
    | Or []  -> False
    | Or [f1] -> aux f1
    | Or lst -> Or(List.map aux (remove_duplicates (flatten_nested_ors lst)))

    (* recurse down the tree *)
    | Relation _ -> f
    | Not f1 -> Not (aux f1)
    | Implication (f1,f2) -> 
      Implication(aux f1,aux f2) 
    | ITE(f1,f2,f3) -> 
      ITE(aux f1,aux f2, aux f3)
    | True|False|UnsupportedFormula _ -> f  
  in  
  aux f

let simplify_terms f = 
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

  let rec aux f = 
    match f with 
  (* base case: something with terms *)
    | Relation(op,t1,t2) -> Relation(op,simplify_term t1, simplify_term t2)

  (* recurse down the tree *)
    | True|False|UnsupportedFormula _ -> f
    | Not f1 -> Not (aux f1)
    | And fl -> And (List.map aux fl)
    | Or  fl -> Or (List.map aux fl)
    | Implication (f1,f2) -> Implication(aux f1,aux f2) 
    | ITE(f1,f2,f3) -> ITE(aux f1,aux f2, aux f3)
  and simplify_term t = 
    match t with
    (* Handle constants *)
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
    | Variable _ | Value _ | UnsupportedTerm _ -> t
  and simplify_vals vals op identity =
    let v = List.fold_left 
      (fun a x -> match x with 
      | Value v -> op a v
      | _ -> failwith "should be only values here"
      ) identity vals in
    (* If + simplified to 0, then no need to add it.  Same for * and 1 *) 
    if v = identity then []
    else [Value(v)]
  in
  aux f

let simplify_formula_2 f =
  let rec aux f = 
    match f with
  (* Logical operators *)
    | And(fs) -> begin match fs with 
      | Relation(LEQ, t1, Value(c1)) :: Relation(LEQ, t2, Value(c2)) :: gs
          when t1 = t2 && (c1 <= c2 || c2 <= c1) ->
        let c = min c1 c2 in
        aux (And(Relation(LEQ,t1, Value(c)) :: gs))
      | Relation(LEQ, t1, Value(c1)) :: Relation(GEQ, t2, Value(c2)) :: gs
      | Relation(EQ, t1, Value(c1)) :: Relation(GEQ, t2, Value(c2)) :: gs
          when t1 = t2 && c1 < c2 ->
        False
      | Relation(LEQ, t1, t2) :: (Relation(LEQ, t3, t4) :: gs) 
      | Relation(LEQ, t1, t2) :: (Relation(GEQ, t4, t3) :: gs)
          when t1 = t4 && t2 = t3 ->
        aux (And (Relation(EQ, t1, t2) :: gs))
      | Relation(LEQ, t1, Value(c1)) :: Relation(LEQ, Value(0), Sum([ t2; Value(c2) ])) :: gs
          when t1 = t2 && c1 = -1 * c2 -> 
        let phi = Relation(EQ,t1, Value(c1)) in
        aux (And (phi :: gs))
      | Relation(LEQ, Value(0), Sum([ t2; Value(c2) ])) :: Relation(LEQ, t1, Value(c1)) :: gs
          when t1 = t2 && c1 = -1 * c2 -> 
        let phi = Relation(EQ,t1, Value(c1)) in
        aux (And(phi :: gs))
      | [ g ] -> aux g
      | [] -> True
      | g :: gs -> 
        let g1 = aux g in
        let
            h = aux (And(gs))
        in
        match h with
        | False -> False
        | True -> g1
        | And(hs) -> And(g1 :: hs)
        | _ -> And([g1; h]) 
    end
    | Or(fs) -> begin match fs with  
      | [ Relation(LEQ, Value(c1), t1) ; Relation(LEQ, t2, Value(c2)) ]
	  when (t1 = t2 && c1 = c2 + 2) ->
        Relation(NEQ, t1, Value(c1 - 1)) (* overflow issues! *)
      | [ Relation(LEQ, t2, Value(c2)) ; Relation(LEQ, Value(c1), t1) ]
	  when (t1 = t2 && c1 = c2 + 2) ->
        Relation(NEQ, t1, Value(c1 - 1)) (* overflow issues! *)
      | _ -> Or(List.map aux fs)
    end

  (* x <= y - 1 ~~~ x < y *)
  (* TODO generalize *)
    | Relation(LEQ, Variable(v1), Sum([ Variable(v2); Value(-1) ])) -> Relation(LT, Variable(v1), Variable(v2))

  (* recurse *)
    | Not f -> Not (aux f)
    | ITE (i,t,e) -> ITE(aux i, aux t, aux e)
    | Implication (f1,f2) -> Implication (aux f1,aux f2)
    | True | False | Relation _ | UnsupportedFormula _ -> f
  in
  aux f

let simplify_formula f = 
  let f = simplify_constants f in
  let f = normalize_formula f in 
  let f = simplify_terms f in
  let f = simplify_formula_2 f in
  let f = propagate_truth_context f in
  f

let rec beautify_formula f =
  let f_simple = simplify_formula f in
  if f = f_simple then
    f_simple
  else
    beautify_formula f_simple