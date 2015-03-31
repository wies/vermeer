open Smtlib_ast
open Smtlib_util

let rec print_formula f indentation =
  match f with
  | Boolvar s -> print_string (indentation ^ s ^ "\n")
  | True -> print_string(indentation ^ "TRUE\n")
  | False -> print_string(indentation ^ "FALSE\n")
  | Not(g) -> print_string(indentation ^ "NOT (\n"); print_formula g (indentation ^ "  "); print_string(indentation ^ ")\n")
  | And(fs) -> print_string(indentation ^ "AND (\n"); List.iter (fun (f2) -> print_formula f2 (indentation ^ "  ")) fs; print_string(indentation ^ ")\n")
  | Or(fs) -> print_string(indentation ^ "OR (\n"); List.iter (fun (f2) -> print_formula f2 (indentation ^ "  ")) fs; print_string(indentation ^ ")\n")
  | Implication(f1, f2) -> print_string(indentation ^ "IMPLICATION (\n"); print_formula f1 (indentation ^ "  "); print_formula f2 (indentation ^ "  "); print_string(indentation ^ ")\n")
  | Relation(rel,t1,t2) -> 
    print_string indentation; 
    print_term t1; 
    print_relation rel;
    print_term t2;
    print_newline ()
  | LinearRelation(op,lst,value) ->
    print_formula (relation_of_linearrelation op lst value) indentation
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
  | Value(v) -> print_int64(v)
  | Sum([ t1 ]) -> print_term t1
  | Sum(t1 :: ts) -> print_string("("); print_term t1; print_string(" + "); print_term (Sum(ts)); print_string(")")
  | Mult [ t1 ]  -> print_term t1
  | Mult(t1 :: ts) -> print_string("("); print_term t1; print_string(" * "); print_term (Mult(ts)); print_string(")")
  | UnsupportedTerm(s) -> print_string("UNSUPPORTED TERM: [" ^ s ^ "]")
  | _ -> print_string("*print_term_TODO*")  

