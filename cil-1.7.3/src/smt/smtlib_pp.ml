(* auto-generated by gt *)

open Smtlib_syntax;;
open Smtlib_ast;;
open Smtlib_simplify;;
open Smtlib_ast_print

module LetMappings = Map.Make(
  struct
    let compare = Pervasives.compare
    type t = symbol
  end
);;


let rec
    translate_to_term smt_term = 
  match smt_term with
  | TermQualIdentifier (_, QualIdentifierId (_, IdSymbol (_, Symbol(_, s)))) ->
    let is_Integer str =
      try ignore(int_of_string str); true with Failure _ -> false (* from http://pleac.sourceforge.net/pleac_ocaml/numbers.html *)
    in
      if is_Integer s then
        let v = int_of_string s in Value(v)
      else
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

  | TermQualIdentifier (p , QualIdentifierId (p2, IdSymbol (p3, Symbol(_, s)))) 
    -> Boolvar s

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


