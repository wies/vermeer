(* auto-generated by gt *)

open Smtlib_syntax;;

module LetMappings = Map.Make(
  struct
    let compare = Pervasives.compare
    type t = symbol
  end
);;

type term = 
| Variable of string
| Value of int 
| Sum of term list
| Mult of term list
| UnsupportedTerm of string
(* division, subtraction? *)
;;

type binop = | EQ | LEQ | LT  | GEQ | GT | NEQ 

type formula = 
| True
| False
| Not of formula
| And of formula list
| Or of formula list
| Implication of formula * formula
(* relations: *)
| Relation of binop * term * term
| ITE of formula * formula * formula
| UnsupportedFormula of string
;; 

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
    | Relation (LEQ, t1,t2) -> term_aux t1; term_aux t2
    | Relation(EQ, t1,t2) -> term_aux t1; term_aux t2
    | Relation(GEQ,t1,t2) -> term_aux t1; term_aux t2
    | Relation(NEQ,t1,t2) -> term_aux t1; term_aux t2
    | Relation(LT,t1,t2) -> term_aux t1; term_aux t2 
    | Relation(GT,t1,t2) -> term_aux t1; term_aux t2
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

let rec print_formula f indentation =
  match f with
  | True -> print_string(indentation ^ "TRUE\n")
  | False -> print_string(indentation ^ "FALSE\n")
  | Not(g) -> print_string(indentation ^ "NOT (\n"); print_formula g (indentation ^ "  "); print_string(indentation ^ ")\n")
  | And(fs) -> print_string(indentation ^ "AND (\n"); List.iter (fun (f2) -> print_formula f2 (indentation ^ "  ")) fs; print_string(indentation ^ ")\n")
  | Or(fs) -> print_string(indentation ^ "OR (\n"); List.iter (fun (f2) -> print_formula f2 (indentation ^ "  ")) fs; print_string(indentation ^ ")\n")
  | Implication(f1, f2) -> print_string(indentation ^ "IMPLICATION (\n"); print_formula f1 (indentation ^ "  "); print_formula f2 (indentation ^ "  "); print_string(indentation ^ ")\n")
  | Relation(LEQ,t1, t2) -> print_string(indentation); print_term t1; print_string(" <= "); print_term t2; print_string("\n")
  | Relation(EQ,t1, t2) -> print_string(indentation); print_term t1; print_string(" = "); print_term t2; print_string("\n")
  | Relation(GEQ,t1, t2) -> print_string(indentation); print_term t1; print_string(" >= "); print_term t2; print_string("\n")
  | Relation(NEQ,t1, t2) -> print_string(indentation); print_term t1; print_string(" != "); print_term t2; print_string("\n")
  | Relation(LT,t1, t2) -> print_string(indentation); print_term t1; print_string(" < "); print_term t2; print_string("\n")
  | Relation(GT,t1, t2) -> print_string(indentation); print_term t1; print_string(" > "); print_term t2; print_string("\n")
  | ITE(f_cond, f_then, f_else) -> 
    print_string(indentation ^ "IF (\n");
    print_formula f_cond (indentation ^ "  ");
    print_string(indentation ^ ") THEN (\n");
    print_formula f_then (indentation ^ "  ");
    print_string(indentation ^ ") ELSE (\n");
    print_formula f_else (indentation ^ "  ");
    print_string(indentation ^ ")\n")
  | UnsupportedFormula(s) -> print_string(indentation ^ "UNSUPPORTED FORMULA: " ^ s ^ "\n")
and
    print_term t = 
  match t with
  | Variable(s) -> print_string(s)
  | Value(v) -> print_int(v)
  | Sum([ t1 ]) -> print_term t1
  | Sum(t1 :: ts) -> print_string("("); print_term t1; print_string(" + "); print_term (Sum(ts)); print_string(")")
  | Mult([t1; t2]) -> print_string("("); print_term t1; print_string(" * "); print_term t2; print_string(")")
  | UnsupportedTerm(s) -> print_string("UNSUPPORTED TERM: [" ^ s ^ "]")
  | _ -> print_string("*print_term_TODO*")  

(* DSN there is probably a better way to do this.
 * What I'm trying to do here is to take advantage of the fact that 
 * A && (A || B), can be simplified to A && (True || B)
 * So, maintain a set of things that are known to be contextually "true"
 * I keep two sets, one which is things which are true here, and one which is 
 * only true for the children.
 * This also holds for implications.
 * A ==> (A && B)  ~~~ A ===> B
 *)

let propegate_truth_context f = 
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
    | Not(False) -> True
    | Not(True) -> False
    | ITE(True,t,e) -> t
    | ITE(False,t,e) -> e
      
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

let op_after_swap oldop = match oldop with
  | EQ  -> EQ 
  | LEQ -> GEQ
  | LT  -> GT
  | GEQ -> LEQ
  | GT  -> LT
  | NEQ -> NEQ

let normalize_formula f = 
  let remove_duplicates fs = 
    let rec uniq = function
      | [] -> []
      | e1 :: e2 :: tl when e1 = e2 -> e1 :: uniq tl
      | hd :: tl -> hd :: uniq tl
    in
    let sorted = List.sort compare fs in
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
    | And fl -> And (List.map aux fl)
    | Or  fl -> Or (List.map aux fl)
    | Implication (f1,f2) -> 
      Implication(aux f1,aux f2) 
    | ITE(f1,f2,f3) -> 
      ITE(aux f1,aux f2, aux f3)
    | True|False|UnsupportedFormula _ -> f
  in
  aux f

let rec simplify_terms f = 
  match f with 
  (* base case: something with terms *)
  | Relation(op,t1,t2) -> Relation(op,simplify_term t1, simplify_term t2)

  (* recurse down the tree *)
  | True|False|UnsupportedFormula _ -> f
  | Not f1 -> Not (simplify_terms f1)
  | And fl -> And (List.map simplify_terms fl)
  | Or  fl -> Or (List.map simplify_terms fl)
  | Implication (f1,f2) -> 
    Implication(simplify_terms f1,simplify_terms f2) 
  | ITE(f1,f2,f3) -> 
    ITE(simplify_terms f1,simplify_terms f2, simplify_terms f3)
and simplify_term t = 
  match t with
  (* Handle constants *)
  | Sum([Value v]) -> Value v
  | Mult([Value v]) -> Value v

  (* Normalize so that sums and mults always have the variable(s) on the left *)
  | Sum(lst) -> 
    let lst = List.map simplify_term lst in
    let (vars,vals,rest) = split_vars_vals lst in
    let vals = simplify_vals vals (+) 0 in
    Sum(vars @ vals  @ rest)
  | Mult(lst) -> 
    let lst = List.map simplify_term lst in
    let (vars,vals,rest) = split_vars_vals lst in
    let vals = simplify_vals vals ( * ) 1 in
    Mult(vars @ vals  @ rest)
  | _ -> t
and simplify_vals vals op init = 
  [Value(
    List.fold_left 
      (fun a x -> match x with 
      | Value v -> op a v
      | _ -> failwith "should be only values here"
      ) init vals
  )]


let rec simplify_formula_2 f =
  match f with
  (* Logical operators *)
  | And(fs) -> begin match fs with 
      | Relation(LEQ,t1, Value(c1)) :: Relation(LEQ,t2, Value(c2)) :: gs
          when t1 = t2 && (c1 <= c2 || c2 <= c1) ->
        let c = min c1 c2 in
        simplify_formula_2 (And(Relation(LEQ,t1, Value(c)) :: gs))
      | Relation(LEQ,t1, t2) :: (Relation(LEQ,t3, t4) :: gs) when (t1 = t4 && t2 = t3) -> 
        (
          let 
              g = simplify_formula_2 (And(gs))
          in
          match g with
          | False -> False
          | True -> Relation(EQ,t1, t2)
          | And(hs) -> let hs2 = (Relation(EQ,t1, t2) :: hs) in And(hs2)
          | _ -> And([ Relation(EQ,t1, t2) ; g ])
        )
      | Relation(LEQ,t1, Value(c1)) :: (Relation(LEQ,Value(0), Sum([ t2; Value(c2) ])) :: gs) when (t1 = t2 && c1 = -1 * c2) -> 
        (
          let phi = Relation(EQ,t1, Value(c1)) in
          let g = simplify_formula_2 (And(gs)) in
          match g with
          | False -> False
          | True -> phi
          | And(hs) -> let hs2 = (phi :: hs) in And(hs2)
          | _ -> And([ phi ; g ])
        )
      | Relation(LEQ,Value(0), Sum([ t2; Value(c2) ])) :: (Relation(LEQ,t1, Value(c1)) :: gs) when (t1 = t2 && c1 = -1 * c2) -> 
        (
          let phi = Relation(EQ,t1, Value(c1)) in
          let g = simplify_formula_2 (And(gs)) in
          match g with
          | False -> False
          | True -> phi
          | And(hs) -> let hs2 = (phi :: hs) in And(hs2)
          | _ -> And([ phi ; g ])
        )
      | [ g ] -> g
      | [] -> True
      | g :: gs -> 
        (
          let
              h = simplify_formula_2 (And(gs))
          in
          match h with
          | False -> False
          | True -> g
          | And(hs) -> let hs2 = (g :: hs) in And(hs2)
          | _ -> And([ g ; h ])
        )
  end
  | Or(fs) -> begin match fs with  
    | [ Relation(LEQ,Value(c1), t1) ; Relation(LEQ,t2, Value(c2)) ] when (t1 = t2 && c1 = c2 + 2) -> Relation(NEQ,t1, Value(c1 - 1)) (* overflow issues! *)
    | [ Relation(LEQ,t2, Value(c2)) ; Relation(LEQ,Value(c1), t1) ] when (t1 = t2 && c1 = c2 + 2) -> Relation(NEQ,t1, Value(c1 - 1)) (* overflow issues! *)
      | _ -> Or(fs)
  end
  | _ -> f

let simplify_formula f = 
  let f = simplify_constants f in
  let f = normalize_formula f in 
  let f = simplify_terms f in
  let f = simplify_formula_2 f in
  let f = propegate_truth_context f in
  f

let rec beautify_formula f =
  let f_simple = simplify_formula f in
  if f = f_simple then
    f_simple
  else
    beautify_formula f_simple
;;

let rec
    translate_to_term smt_term = 
  match smt_term with
  | TermQualIdentifier (_, QualIdentifierId (_, IdSymbol (_, Symbol(_, s)))) ->
    Variable(s)

  | TermSpecConst (_, SpecConstNum(_, c)) -> 
    let
        v = int_of_string c
    in
    Value(v)

  | TermQualIdTerm (_, QualIdentifierId(_, IdSymbol (_, Symbol(_, "+"))), (_, [ t1 ])) ->
    let 
        t1_trans = translate_to_term t1
    in
    t1_trans

  | TermQualIdTerm (_, QualIdentifierId(_, IdSymbol (_, Symbol(_, "+"))), (_, ts)) ->
    let 
        ts_trans = List.map translate_to_term ts
    in
    Sum( ts_trans )

  | TermQualIdTerm (_, QualIdentifierId(_, IdSymbol (_, Symbol(_, "-"))), (_, [ TermSpecConst (_, SpecConstNum(_, c)) ])) ->
    let
        v = int_of_string c
    in
    let
        v2 = -1 * v
    in
    Value(v2)

  | TermQualIdTerm (_, QualIdentifierId(_, IdSymbol (_, Symbol(_, "*"))), (_, [ t1; t2 ])) ->
    let 
        t1_trans = translate_to_term t1
    in
    let
        t2_trans = translate_to_term t2
    in
    Mult([ t1_trans; t2_trans ])

  | TermQualIdTerm (_, QualIdentifierId(_, IdSymbol (_, Symbol(_, s))), (_, [ TermQualIdentifier (_, QualIdentifierId (_, IdSymbol (_, Symbol(_, s2)))) ])) ->
    let
	term1 = Value(-1)
    in
    let
	term2 = Variable(s2)
    in
    Mult([ term1; term2 ])

  | TermQualIdTerm (_, QualIdentifierId(_, IdSymbol (_, Symbol(_, s))), _) ->
    UnsupportedTerm("Case#1_" ^ s)

  | _ -> UnsupportedTerm("Case#2")
and
    translate_to_formula smt_term =
  match smt_term with 
  |TermSpecConst (p , specconstant1) -> 
    UnsupportedFormula("TermSpecConst")

  |TermQualIdentifier (p , QualIdentifierId (p2, IdSymbol (p3, Symbol(_, "true") ))) -> 
    True

  |TermQualIdentifier (p , QualIdentifierId (p2, IdSymbol (p3, Symbol(_, "false") ))) -> 
    False

  |TermQualIdentifier (p , QualIdentifierId (p2, IdSymbol (p3, Symbol(_, s)))) ->
    UnsupportedFormula("TermQualIdentifier: " ^ s)

  |TermQualIdentifier (p , QualIdentifierId (p2, IdSymbol (p3, sym))) -> 
    UnsupportedFormula("TermQualIdentifier1")

  |TermQualIdentifier (p , QualIdentifierId (p2, IdUnderscoreSymNum (p3, sym, n))) -> 
    UnsupportedFormula("TermQualIdentifier2")

  |TermQualIdentifier (p , QualIdentifierAs (p2, id, s)) -> 
    UnsupportedFormula("TermQualIdentifier3")

  |TermQualIdTerm (p , QualIdentifierId(_, IdSymbol (_, Symbol(_, "<="))), (_, [ t1; t2 ])) -> 
    let
	t1_trans = translate_to_term t1
    in
    let
        t2_trans = translate_to_term t2
    in 
    Relation(LEQ,t1_trans, t2_trans)

  |TermQualIdTerm (p , QualIdentifierId(_, IdSymbol (_, Symbol(_, ">="))), (_, [ t1; t2 ])) -> 
    let
	t1_trans = translate_to_term t1
    in
    let
        t2_trans = translate_to_term t2
    in 
    Relation(GEQ,t1_trans, t2_trans)

  |TermQualIdTerm (p , QualIdentifierId(_, IdSymbol (_, Symbol(_, "="))), (_, [ t1; t2 ])) -> 
    let
	t1_trans = translate_to_term t1
    in
    let
        t2_trans = translate_to_term t2
    in 
    Relation(EQ,t1_trans, t2_trans)

  |TermQualIdTerm (p , QualIdentifierId(_, IdSymbol (_, Symbol(_, "distinct"))), (_, [ t1; t2 ])) -> 
    let
	t1_trans = translate_to_term t1
    in
    let
        t2_trans = translate_to_term t2
    in 
    Relation(NEQ,t1_trans, t2_trans)

  |TermQualIdTerm (p , QualIdentifierId(_, IdSymbol (_, Symbol(_, ">"))), (_, [ t1; t2 ])) -> 
    let
	t1_trans = translate_to_term t1
    in
    let
        t2_trans = translate_to_term t2
    in 
    Relation(GT,t1_trans, t2_trans)

  |TermQualIdTerm (p , QualIdentifierId(_, IdSymbol (_, Symbol(_, "<"))), (_, [ t1; t2 ])) -> 
    let
	t1_trans = translate_to_term t1
    in
    let
        t2_trans = translate_to_term t2
    in 
    Relation(LT,t1_trans, t2_trans)

  | TermQualIdTerm (_, QualIdentifierId(_, IdSymbol (_, Symbol(_, "or"))), (_, ts)) ->
    let
	ts2 = List.map translate_to_formula ts
    in
    Or( ts2 )

  | TermQualIdTerm (_, QualIdentifierId(_, IdSymbol (_, Symbol(_, "and"))), (_, ts)) ->
    let
	ts2 = List.map translate_to_formula ts
    in
    And( ts2 )

  | TermQualIdTerm (p , QualIdentifierId(_, IdSymbol (_, Symbol(_, "=>"))), (_, [ f1; f2 ])) -> 
    let
	f1_trans = translate_to_formula f1
    in
    let
        f2_trans = translate_to_formula f2
    in 
    Implication(f1_trans, f2_trans)

  |TermQualIdTerm (p , QualIdentifierId(_, IdSymbol (_, Symbol(_, "ite"))), (p2, ts)) -> 
    ITE(translate_to_formula (List.nth ts 0), translate_to_formula (List.nth ts 1), translate_to_formula (List.nth ts 2))

  |TermQualIdTerm (p , QualIdentifierId(_, IdSymbol (_, Symbol(_, "not"))), (p2, ts)) -> 
    Not(translate_to_formula (List.nth ts 0))

  |TermQualIdTerm (p , QualIdentifierId(_, IdSymbol (_, Symbol(_, s))), (p2, ts)) -> 
    UnsupportedFormula("TermQualIdTerm1! " ^ s ^ "\n")

  |TermQualIdTerm (p , QualIdentifierId(_, id), (p2, ts)) -> 
    UnsupportedFormula("TermQualIdTerm2")

  |TermQualIdTerm (p , QualIdentifierAs(_, id, s) , (p2, ts)) -> 
    UnsupportedFormula("TermQualIdTerm3")

  |TermLetTerm (p , termletterm_term_varbinding584 , t2) -> 
    raise (Failure "Let terms are not allowed!\n")

  |TermForAllTerm (p , t_var , t2) -> 
    UnsupportedFormula("TermForAllTerm")

  |TermExistsTerm (p , t_var , t2) -> 
    UnsupportedFormula("TermExistsTerm")

  |TermExclimationPt (p , t2 , termexclimationpt_term_attribute644) -> 
    UnsupportedFormula("TermExclimationPt")
;;

let rec 
    to_let_mapping bindings m = 
  match bindings with
  | [] -> LetMappings.empty
  | (VarBindingSymTerm (_ , s , t))::ts -> LetMappings.add s (eliminate_let_terms t m) (to_let_mapping ts m)
and
    create_let_mapping p m =
  match p with
  | (_, ls) -> to_let_mapping ls m
and
    print_let_mapping s t =
  match s with
  | Symbol (_, name) -> print_string(name ^ "\n")
  | SymbolWithOr (_, name) -> print_string(name ^ "\n")
and 
    apply_let_mapping t m = 
  match t with
  |TermSpecConst (_ , specconstant1) -> ()
  |TermQualIdentifier (_ , qualidentifier1) -> ()
  |TermQualIdTerm (_ , qualidentifier2 , termqualidterm_term_term563) -> ()
  |TermLetTerm (_ , termletterm_term_varbinding584 , term6) -> ()
  |TermForAllTerm (_ , termforallterm_term_sortedvar604 , term6) -> ()
  |TermExistsTerm (_ , termexiststerm_term_sortedvar624 , term6) -> ()
  |TermExclimationPt (_ , term3 , termexclimationpt_term_attribute644) -> ()
and
    eliminate_let_terms t m =
  match t with
  |TermSpecConst (p , specconstant1) -> t

  |TermQualIdentifier (p , QualIdentifierId (p2, IdSymbol (p3, sym))) -> 
    (try
       let 
           t_new = LetMappings.find sym m 
       in
       t_new
     with 
       Not_found -> t)

  |TermQualIdentifier (p , QualIdentifierId (p2, IdUnderscoreSymNum (p3, sym, n))) -> t

  |TermQualIdentifier (p , QualIdentifierAs (p2, id, s)) -> t

  |TermQualIdTerm (p , qualidentifier2 , (p2, ts)) -> 
    let
	ts2 = List.map (fun t2 -> eliminate_let_terms t2 m) ts
    in 
    TermQualIdTerm (p, qualidentifier2, (p2, ts2))

  |TermLetTerm (p , termletterm_term_varbinding584 , t2) -> 
    let 
	m2 = create_let_mapping termletterm_term_varbinding584 m
    in 
    eliminate_let_terms t2 (LetMappings.merge (fun k v1 v2 -> match v1, v2 with | _, Some v -> Some v | Some v, None -> Some v | None, None -> None) m m2)

  |TermForAllTerm (p , t_var , t2) -> 
    let
	t2_prime = eliminate_let_terms t2 m
    in
    TermForAllTerm (p, t_var, t2_prime)

  |TermExistsTerm (p , t_var , t2) -> 
    let
	t2_prime = eliminate_let_terms t2 m
    in
    TermExistsTerm (p, t_var, t2_prime)

  |TermExclimationPt (p , t2 , termexclimationpt_term_attribute644) -> 
    let 
	t2_prime = eliminate_let_terms t2 m 
    in 
    TermExclimationPt (p, t2_prime, termexclimationpt_term_attribute644)
;;



let rec dummy () = () 
and pp_an_option = function 
  |AnOptionAttribute (_ , attribute1) ->  pp_attribute attribute1; () 
and pp_attribute = function 
  |AttributeKeyword (_ , str1) ->  print_string str1; () 
  |AttributeKeywordValue (_ , str1 , attributevalue2) ->  print_string str1;print_string " "; pp_attributevalue attributevalue2; () 
and pp_attributevalue = function 
  |AttributeValSpecConst (_ , specconstant1) ->  pp_specconstant specconstant1; () 
  |AttributeValSymbol (_ , symbol1) ->  pp_symbol symbol1; () 
  |AttributeValSexpr (_ , attributevalsexpr_attributevalue_sexpr52) ->  print_string "(";print_string " "; pp_attributevalsexpr_attributevalue_sexpr5 attributevalsexpr_attributevalue_sexpr52;print_string " "; print_string ")"; () 
and pp_command = function 
  |CommandSetLogic (_ , symbol3) ->  print_string "(";print_string " "; print_string "set-logic";print_string " "; pp_symbol symbol3;print_string " "; print_string ")"; () 
  |CommandSetOption (_ , an_option3) ->  print_string "(";print_string " "; print_string "set-option";print_string " "; pp_an_option an_option3;print_string " "; print_string ")"; () 
  |CommandSetInfo (_ , attribute3) ->  print_string "(";print_string " "; print_string "set-info";print_string " "; pp_attribute attribute3;print_string " "; print_string ")"; () 
  |CommandDeclareSort (_ , symbol3 , str4) ->  print_string "(";print_string " "; print_string "declare-sort";print_string " "; pp_symbol symbol3;print_string " "; print_string str4;print_string " "; print_string ")"; () 
  |CommandDefineSort (_ , symbol3 , commanddefinesort_command_symbol115 , sort7) ->  print_string "(";print_string " "; print_string "define-sort";print_string " "; pp_symbol symbol3;print_string " "; print_string "(";print_string " "; pp_commanddefinesort_command_symbol11 commanddefinesort_command_symbol115;print_string " "; print_string ")";print_string " "; pp_sort sort7;print_string " "; print_string ")"; () 
  |CommandDeclareFun (_ , symbol3 , commanddeclarefun_command_sort135 , sort7) ->  print_string "(";print_string " "; print_string "declare-fun";print_string " "; pp_symbol symbol3;print_string " "; print_string "(";print_string " "; pp_commanddeclarefun_command_sort13 commanddeclarefun_command_sort135;print_string " "; print_string ")";print_string " "; pp_sort sort7;print_string " "; print_string ")"; () 
  |CommandDefineFun (_ , symbol3 , commanddefinefun_command_sortedvar155 , sort7 , term8) ->  print_string "(";print_string " "; print_string "define-fun";print_string " "; pp_symbol symbol3;print_string " "; print_string "(";print_string " "; pp_commanddefinefun_command_sortedvar15 commanddefinefun_command_sortedvar155;print_string " "; print_string ")";print_string " "; pp_sort sort7;print_string " "; pp_term term8;print_string " "; print_string ")"; () 
  |CommandPush (_ , str3) ->  print_string "(";print_string " "; print_string "push";print_string " "; print_string str3;print_string " "; print_string ")"; () 
  |CommandPop (_ , str3) ->  print_string "(";print_string " "; print_string "pop";print_string " "; print_string str3;print_string " "; print_string ")"; () 

  (* this is the important command case *)
  |CommandAssert (_ , term3) ->  (* pp_term term3; () *)
    let 
        t = eliminate_let_terms term3 LetMappings.empty
    in 
    let 
        f = translate_to_formula t
    in 
    let
        f_simple = beautify_formula f
    in
    print_formula f_simple ""; () 

  |CommandCheckSat (_) ->  print_string "(";print_string " "; print_string "check-sat";print_string " "; print_string ")"; () 
  |CommandGetAssert (_) ->  print_string "(";print_string " "; print_string "get-assertions";print_string " "; print_string ")"; () 
  |CommandGetProof (_) ->  print_string "(";print_string " "; print_string "get-proof";print_string " "; print_string ")"; () 
  |CommandGetUnsatCore (_) ->  print_string "(";print_string " "; print_string "get-unsat-core";print_string " "; print_string ")"; () 
  |CommandGetValue (_ , commandgetvalue_command_term244) ->  print_string "(";print_string " "; print_string "get-value";print_string " "; print_string "(";print_string " "; pp_commandgetvalue_command_term24 commandgetvalue_command_term244;print_string " "; print_string ")";print_string " "; print_string ")"; () 
  |CommandGetAssign (_) ->  print_string "(";print_string " "; print_string "get-assignment";print_string " "; print_string ")"; () 
  |CommandGetOption (_ , str3) ->  print_string "(";print_string " "; print_string "get-option";print_string " "; print_string str3;print_string " "; print_string ")"; () 
  |CommandGetInfo (_ , infoflag3) ->  print_string "(";print_string " "; print_string "get-info";print_string " "; pp_infoflag infoflag3;print_string " "; print_string ")"; () 
  |CommandExit (_) ->  print_string "(";print_string " "; print_string "exit";print_string " "; print_string ")"; () 
and pp_commands = function 
  |Commands (_ , commands_commands_command301) ->  pp_commands_commands_command30 commands_commands_command301; () 
and pp_identifier = function 
  |IdSymbol (_ , Symbol(_, "<=")) -> print_string "holla"; ()
  |IdSymbol (_ , symbol1) ->  print_string "&"; pp_symbol symbol1; () 
  |IdUnderscoreSymNum (_ , symbol3 , idunderscoresymnum_identifier_numeral334) ->  print_string "(";print_string " "; print_string "_";print_string " "; pp_symbol symbol3;print_string " "; pp_idunderscoresymnum_identifier_numeral33 idunderscoresymnum_identifier_numeral334;print_string " "; print_string ")"; () 
and pp_infoflag = function 
  |InfoFlagKeyword (_ , str1) ->  print_string str1; () 
and pp_qualidentifier = function 
  |QualIdentifierId (_ , identifier1) ->  pp_identifier identifier1; () 
  |QualIdentifierAs (_ , identifier3 , sort4) ->  print_string "(";print_string " "; print_string "as";print_string " "; pp_identifier identifier3;print_string " "; pp_sort sort4;print_string " "; print_string ")"; () 
and pp_sexpr = function 
  |SexprSpecConst (_ , specconstant1) ->  pp_specconstant specconstant1; () 
  |SexprSymbol (_ , symbol1) ->  pp_symbol symbol1; () 
  |SexprKeyword (_ , str1) ->  print_string str1; () 
  |SexprInParen (_ , sexprinparen_sexpr_sexpr412) ->  print_string "(";print_string " "; pp_sexprinparen_sexpr_sexpr41 sexprinparen_sexpr_sexpr412;print_string " "; print_string ")"; () 
and pp_sort = function 
  |SortIdentifier (_ , identifier1) ->  pp_identifier identifier1; () 
  |SortIdSortMulti (_ , identifier2 , sortidsortmulti_sort_sort443) ->  print_string "(";print_string " "; pp_identifier identifier2;print_string " "; pp_sortidsortmulti_sort_sort44 sortidsortmulti_sort_sort443;print_string " "; print_string ")"; () 
and pp_sortedvar = function 
  |SortedVarSymSort (_ , symbol2 , sort3) ->  print_string "(";print_string " "; pp_symbol symbol2;print_string " "; pp_sort sort3;print_string " "; print_string ")"; () 
and pp_specconstant = function 
  |SpecConstsDec (_ , str1) ->  print_string str1; () 
  |SpecConstNum (_ , str1) ->  print_string str1; () 
  |SpecConstString (_ , str1) ->  print_string str1; () 
  |SpecConstsHex (_ , str1) ->  print_string str1; () 
  |SpecConstsBinary (_ , str1) ->  print_string str1; () 
and pp_symbol = function 
  |Symbol (_ , str1) ->  print_string str1; () 
  |SymbolWithOr (_ , str1) ->  print_string str1; () 


and pp_term = function (* simplification is done here *)

  |TermSpecConst (_ , specconstant1) ->  print_string "#"; pp_specconstant specconstant1; () 

  |TermQualIdentifier (_ , qualidentifier1) ->  print_string "@"; pp_qualidentifier qualidentifier1; () 

  |TermQualIdTerm (_ , qualidentifier2 , termqualidterm_term_term563) ->  print_string "(";print_string " "; pp_qualidentifier qualidentifier2;print_string " "; pp_termqualidterm_term_term56 termqualidterm_term_term563;print_string " "; print_string ")"; () 

  |TermLetTerm (p , termletterm_term_varbinding584 , term6) ->  
    let 
	t = eliminate_let_terms (TermLetTerm (p , termletterm_term_varbinding584 , term6)) LetMappings.empty 
    in 
    pp_term t; () 

  |TermForAllTerm (_ , termforallterm_term_sortedvar604 , term6) ->  
    print_string "(";print_string " "; print_string "forall";print_string " "; print_string "(";print_string " "; pp_termforallterm_term_sortedvar60 termforallterm_term_sortedvar604;print_string " "; print_string ")";print_string " "; pp_term term6;print_string " "; print_string ")"; () 

  |TermExistsTerm (_ , termexiststerm_term_sortedvar624 , term6) ->  print_string "(";print_string " "; print_string "exists";print_string " "; print_string "(";print_string " "; pp_termexiststerm_term_sortedvar62 termexiststerm_term_sortedvar624;print_string " "; print_string ")";print_string " "; pp_term term6;print_string " "; print_string ")"; () 

  |TermExclimationPt (_ , term3 , termexclimationpt_term_attribute644) ->  print_string "(";print_string " "; print_string "!";print_string " "; pp_term term3;print_string " "; pp_termexclimationpt_term_attribute64 termexclimationpt_term_attribute644;print_string " "; print_string ")"; () 


and pp_varbinding = function 
  |VarBindingSymTerm (_ , symbol2 , term3) ->  print_string "(";print_string " "; pp_symbol symbol2;print_string " represents "; pp_term term3;print_string " "; print_string ")"; () 
and pp_termexclimationpt_term_attribute64 = function 
  |(_,[]) ->   () 
  | (d , (attribute1)::termexclimationpt_term_attribute642) ->  pp_attribute attribute1;print_string " "; pp_termexclimationpt_term_attribute64 (d,termexclimationpt_term_attribute642); () 
and pp_termexiststerm_term_sortedvar62 = function 
  |(_,[]) ->   () 
  | (d , (sortedvar1)::termexiststerm_term_sortedvar622) ->  pp_sortedvar sortedvar1;print_string " "; pp_termexiststerm_term_sortedvar62 (d,termexiststerm_term_sortedvar622); () 
and pp_termforallterm_term_sortedvar60 = function 
  |(_,[]) ->   () 
  | (d , (sortedvar1)::termforallterm_term_sortedvar602) ->  pp_sortedvar sortedvar1;print_string " "; pp_termforallterm_term_sortedvar60 (d,termforallterm_term_sortedvar602); () 
and pp_termletterm_term_varbinding58 = function 
  |(_,[]) ->   () 
  | (d , (varbinding1)::termletterm_term_varbinding582) ->  pp_varbinding varbinding1;print_string " "; pp_termletterm_term_varbinding58 (d,termletterm_term_varbinding582); () 
and pp_termqualidterm_term_term56 = function 
  |(_,[]) ->   () 
  | (d , (term1)::termqualidterm_term_term562) ->  pp_term term1;print_string " "; pp_termqualidterm_term_term56 (d,termqualidterm_term_term562); () 
and pp_sortidsortmulti_sort_sort44 = function 
  |(_,[]) ->   () 
  | (d , (sort1)::sortidsortmulti_sort_sort442) ->  pp_sort sort1;print_string " "; pp_sortidsortmulti_sort_sort44 (d,sortidsortmulti_sort_sort442); () 
and pp_sexprinparen_sexpr_sexpr41 = function 
  |(_,[]) ->   () 
  | (d , (sexpr1)::sexprinparen_sexpr_sexpr412) ->  pp_sexpr sexpr1;print_string " "; pp_sexprinparen_sexpr_sexpr41 (d,sexprinparen_sexpr_sexpr412); () 
and pp_idunderscoresymnum_identifier_numeral33 = function 
  |(_,[]) ->   () 
  | (d , (str1)::idunderscoresymnum_identifier_numeral332) ->  print_string str1;print_string " "; pp_idunderscoresymnum_identifier_numeral33 (d,idunderscoresymnum_identifier_numeral332); () 
and pp_commands_commands_command30 = function 
  |(_,[]) ->   () 
  | (d , (command1)::commands_commands_command302) ->  pp_command command1;print_string " "; pp_commands_commands_command30 (d,commands_commands_command302); () 
and pp_commandgetvalue_command_term24 = function 
  |(_,[]) ->   () 
  | (d , (term1)::commandgetvalue_command_term242) ->  pp_term term1;print_string " "; pp_commandgetvalue_command_term24 (d,commandgetvalue_command_term242); () 
and pp_commanddefinefun_command_sortedvar15 = function 
  |(_,[]) ->   () 
  | (d , (sortedvar1)::commanddefinefun_command_sortedvar152) ->  pp_sortedvar sortedvar1;print_string " "; pp_commanddefinefun_command_sortedvar15 (d,commanddefinefun_command_sortedvar152); () 
and pp_commanddeclarefun_command_sort13 = function 
  |(_,[]) ->   () 
  | (d , (sort1)::commanddeclarefun_command_sort132) ->  pp_sort sort1;print_string " "; pp_commanddeclarefun_command_sort13 (d,commanddeclarefun_command_sort132); () 
and pp_commanddefinesort_command_symbol11 = function 
  |(_,[]) ->   () 
  | (d , (symbol1)::commanddefinesort_command_symbol112) ->  pp_symbol symbol1;print_string " "; pp_commanddefinesort_command_symbol11 (d,commanddefinesort_command_symbol112); () 
and pp_attributevalsexpr_attributevalue_sexpr5 = function 
  |(_,[]) ->   () 
  | (d , (sexpr1)::attributevalsexpr_attributevalue_sexpr52) ->  pp_sexpr sexpr1;print_string " "; pp_attributevalsexpr_attributevalue_sexpr5 (d,attributevalsexpr_attributevalue_sexpr52); () ;;
let pp e = pp_commands e;;


