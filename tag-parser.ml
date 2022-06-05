#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;

let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

(*---------------- helpers ------------------*)
(* try to use given methods instead ! *)
let rec string_list lst = (*Can be replaced by scm_list_to_list!!!*)
  match lst with
  | ScmNil -> []
  | ScmPair(ScmSymbol(x), exprs) -> x::(string_list exprs) (*the ScmSymbol is the difference*)
  | _ -> raise (X_syntax_error (lst, "lst structure not recognized"))

let rec string_improper_list lst =
  match lst with
  | ScmSymbol(x) -> []
  | ScmPair(ScmSymbol(x), ScmSymbol(_)) -> [x]
  | ScmPair(ScmSymbol(x), exprs) -> x::(string_improper_list exprs)
  | _ -> raise (X_syntax_error (lst, "lst structure not recognized"))

let rec get_last_item lst =
  match lst with
  | ScmSymbol(x) -> x
  | ScmPair(ScmSymbol(_), ScmSymbol(expr)) -> expr
  | ScmPair(ScmSymbol(_), exprs) -> (get_last_item exprs)
  | _ -> raise (X_syntax_error (lst, "lst structure not recognized"))

let flat_seq exp =
  match exp with
  | ScmSeq(x) -> x
  | x -> [x];;
(*-------------- end helpers ----------------*)

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with 
(* Implement tag parsing here *)
(*-------------------------------------------*)
(* Constants *)
| ScmNil -> ScmConst(ScmVoid)
| ScmBoolean(x) -> ScmConst(ScmBoolean(x))
| ScmChar(x) -> ScmConst(ScmChar(x))
| ScmNumber(x) -> ScmConst(ScmNumber(x))
| ScmString(x) -> ScmConst(ScmString(x))
| ScmVector(x) -> ScmConst(ScmVector(x))
| ScmPair(ScmSymbol("quote"), ScmPair(x, ScmNil)) -> ScmConst(x)

(* Variables *)
| ScmSymbol(x) -> if (List.mem x reserved_word_list) then raise (X_reserved_word x) else ScmVar(x)

(* Conditionals *)
| ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmPair(dif, ScmNil)))) ->
                ScmIf(tag_parse_expression test, tag_parse_expression dit, tag_parse_expression dif)
| ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmNil))) ->
                ScmIf(tag_parse_expression test, tag_parse_expression dit, ScmConst(ScmVoid))

(* Disjunctions *)
| ScmPair(ScmSymbol("or"), ScmNil) -> ScmConst(ScmBoolean(false))
| ScmPair(ScmSymbol("or"), ScmPair(expr, ScmNil)) -> tag_parse_expression expr
| ScmPair(ScmSymbol("or"), exprs) -> ScmOr(List.map tag_parse_expression (scm_list_to_list exprs))

(* Lambda forms *)
| ScmPair(ScmSymbol("lambda"), ScmPair(vars, exprs)) -> handle_lambda vars exprs
  (* Simple lambda *)
  (* Lambda with optional arguments *)
  (* Variadic lambda *)

(* Define *)
(* MIT-style define *)
| ScmPair(ScmSymbol("define"), ScmPair(ScmPair(var, args), body)) ->
    if (is_var var) then
        tag_parse_expression (ScmPair(ScmSymbol("define"), ScmPair(var, ScmPair(ScmPair(ScmSymbol("lambda"), ScmPair(args, body)), ScmNil))))
    else raise (X_syntax_error (var, "var is not of type ScmVar"))
(* Simple define *)
| ScmPair(ScmSymbol("define"), ScmPair(var, ScmPair(value, ScmNil))) ->
    if (is_var var) then
      ScmDef(tag_parse_expression var, tag_parse_expression value)
    else raise (X_syntax_error (var, "var is not of type ScmVar"))

(* Assignments *)
| ScmPair(ScmSymbol("set!"), ScmPair(var, ScmPair(value, ScmNil))) ->
    if (is_var var) then
      ScmSet(tag_parse_expression var, tag_parse_expression value)
    else raise (X_syntax_error (var, "var is not of type ScmVar"))

(* Sequences *)
(* Explicit - begin-expression *)
| ScmPair(ScmSymbol("begin"), exprs) -> handle_sequence exprs

(* Applications *)
| ScmPair(exp1, exprs) -> ScmApplic(tag_parse_expression exp1, List.map tag_parse_expression (scm_list_to_list exprs))
(*-------------------------------------------*)
| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))

(*---------------- helpers ------------------*)
and is_var sexpr =
  let parsed_expr = tag_parse_expression sexpr in
  match parsed_expr with
  | ScmVar(_) -> true
  | _ -> false
(* -------------------- *)
and handle_lambda vars exprs =
  let lambda_type = scm_is_list vars in
  match lambda_type with
  | true -> ScmLambdaSimple(string_list vars, handle_sequence exprs)
  | false -> ScmLambdaOpt(string_improper_list vars, get_last_item vars, handle_sequence exprs)

and handle_sequence exprs =
  let sequence_expr = make_sequence exprs in
  if List.length sequence_expr = 1 then
      List.nth sequence_expr 0 else
      ScmSeq(sequence_expr)

and make_sequence seq =
  match seq with
  | ScmNil -> []
  | ScmPair(ScmSymbol("begin"), expr) -> make_sequence expr
  | ScmPair(expr, exprs) -> tag_parse_expression expr::make_sequence(exprs)
  | _ -> raise (X_syntax_error (seq, "seq structure not recognized"))
(*-------------- end helpers ----------------*)

and macro_expand sexpr =
match sexpr with
(* Handle macro expansion patterns here *)
(*-------------------------------------------*)
(* let *) 
| ScmPair(ScmSymbol("let"), ScmPair(ScmNil, body)) -> macro_expand (ScmPair(ScmPair(ScmSymbol("lambda"), ScmPair(ScmNil, body)), ScmNil))
| ScmPair(ScmSymbol("let"), ScmPair(ScmPair(rib, ribs), body)) -> handle_let rib ribs body
(* let* *)
| ScmPair(ScmSymbol("let*"), ScmPair(ScmNil, body)) -> macro_expand (ScmPair(ScmSymbol("let"), ScmPair(ScmNil, body)))
| ScmPair(ScmSymbol("let*"), ScmPair(ScmPair(rib, ribs), body)) -> handle_let_star rib ribs body
(* letrec *)
| ScmPair(ScmSymbol("letrec"), ScmPair(ScmNil, body)) -> macro_expand (ScmPair(ScmSymbol("let"), ScmPair(ScmNil, body)))
| ScmPair(ScmSymbol("letrec"), ScmPair(ScmPair(rib, ribs), body)) -> handle_letrec rib ribs body

(* and *)
| ScmPair(ScmSymbol("and"), ScmNil) -> ScmBoolean(true)
| ScmPair(ScmSymbol("and"), ScmPair(expr, ScmNil)) -> macro_expand expr
| ScmPair(ScmSymbol("and"), ScmPair(expr, exprs)) ->
      macro_expand (ScmPair(ScmSymbol("if"), ScmPair(expr, ScmPair(ScmPair(ScmSymbol("and"), exprs), ScmPair(ScmBoolean(false), ScmNil)))))

(* cond *)
| ScmPair(ScmSymbol("cond"), ribs) -> handle_cond ribs

(* quasiquote *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(sexpr, ScmNil)) -> macro_expand (handle_quasi_quote sexpr)
| ScmPair(ScmSymbol("quasiquote"), sexpr) -> macro_expand (handle_quasi_quote sexpr)
(*-------------------------------------------*)
| _ -> sexpr

(*---------------- helpers ------------------*)
(*-----------let-------------*)
and handle_let rib ribs body =
  let vars = list_to_proper_list (let_expr_list rib ribs) in
  let values = list_to_proper_list (let_exprs_list rib ribs) in
  macro_expand (ScmPair(ScmPair(ScmSymbol("lambda"), ScmPair(vars, body)), values))

and let_expr_list rib ribs =
  let extract_vars =
    match rib with
    | ScmPair(var, ScmPair(_, ScmNil)) -> var
    | _ -> raise (X_syntax_error (rib, "rib structure not recognized")) in
  match ribs with
  | ScmPair(exp, exprs) -> extract_vars::(let_expr_list exp exprs)
  | ScmNil -> [extract_vars]
  | _ -> raise (X_syntax_error (ribs, "ribs structure not recognized"))

and let_exprs_list rib ribs =
  let extract_values =
    match rib with
    | ScmPair(_, ScmPair(value, ScmNil)) -> value
    | _ -> raise (X_syntax_error (rib, "rib structure not recognized")) in
  match ribs with
  | ScmPair(exp, exprs) -> extract_values::(let_exprs_list exp exprs)
  | ScmNil -> [extract_values]
  | _ -> raise (X_syntax_error (rib, "rib structure not recognized"))

and handle_let_star rib ribs body =
  match ribs with
  | ScmNil -> macro_expand (ScmPair(ScmSymbol("let"), ScmPair(ScmPair(rib, ScmNil), body)))
  | _ -> macro_expand (ScmPair(ScmSymbol("let"), ScmPair(ScmPair(rib, ScmNil), ScmPair(ScmPair(ScmSymbol("let*"), ScmPair(ribs, body)), ScmNil))))

and handle_letrec rib ribs body =
  let exprs = letrec_whatever_list (ScmPair(rib, ribs)) in
  let sets_and_body = handle_vars (ScmPair(rib, ribs)) body in
  macro_expand (ScmPair(ScmSymbol("let"), ScmPair(exprs, sets_and_body)))

and letrec_whatever_list exprs =
  match exprs with
  | ScmPair(ScmPair(exp, ScmPair(_, ScmNil)), ScmNil) ->
      ScmPair(ScmPair(exp, ScmPair(ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol("whatever"), ScmNil)), ScmNil)), ScmNil)
  | ScmPair(ScmPair(exp, ScmPair(_, ScmNil)), cdr) ->
      ScmPair(ScmPair(exp, ScmPair(ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol("whatever"), ScmNil)), ScmNil)), (letrec_whatever_list cdr))
  | _ -> raise (X_syntax_error (exprs, "exprs structure not recognized"))

and handle_vars exprs body =
  match exprs with
  | ScmPair(ScmPair(exp, ScmPair(value, ScmNil)), ScmNil) ->
      ScmPair(ScmPair(ScmSymbol("set!"), ScmPair(exp, ScmPair(value, ScmNil))), body)
  | ScmPair(ScmPair(exp, ScmPair(value, ScmNil)), cdr) ->
      ScmPair(ScmPair(ScmSymbol("set!"), ScmPair(exp, ScmPair(value, ScmNil))), (handle_vars cdr body))
  | _ -> raise (X_syntax_error (exprs, "exprs structure not recognized"))

(*------------cond------------*)
and handle_cond ribs =
  match ribs with
  | ScmNil -> ScmNil
  | ScmPair(rib, ribs) -> cond_type rib ribs
  | _ -> raise (X_syntax_error (ribs, "ribs structure not recognized"))

and cond_type rib ribs =
  match rib with
  | ScmPair(expr, ScmPair(ScmSymbol("=>"), ScmPair(exprs, ScmNil))) ->
          macro_expand
          (ScmPair(ScmSymbol("let"), ScmPair(ScmPair(ScmPair(ScmSymbol("value"), ScmPair(expr, ScmNil)),
            ScmPair(ScmPair(ScmSymbol("f"), ScmPair(ScmPair(ScmSymbol("lambda"), ScmPair(ScmNil, ScmPair(exprs, ScmNil))), ScmNil)),
            ScmPair(ScmPair(ScmSymbol("rest"), ScmPair(ScmPair(ScmSymbol("lambda"), ScmPair(ScmNil, ScmPair(handle_cond ribs, ScmNil))), ScmNil)),ScmNil))),
            ScmPair(ScmPair(ScmSymbol("if"), ScmPair(ScmSymbol("value"),
            ScmPair(ScmPair(ScmPair(ScmSymbol("f"), ScmNil), ScmPair(ScmSymbol("value"), ScmNil)),
            ScmPair(ScmPair(ScmSymbol("rest"), ScmNil), ScmNil)))), ScmNil))))
  | ScmPair(ScmSymbol("else"), exprs) ->
          macro_expand (ScmPair(ScmSymbol("begin"), exprs))
  | ScmPair(cond, exprs) ->
          macro_expand
          (ScmPair(ScmSymbol("if"), ScmPair(cond, ScmPair(ScmPair(ScmSymbol("begin"), exprs), ScmPair(handle_cond ribs, ScmNil)))))
  | _ -> raise (X_syntax_error (rib, "rib structure not recognized"))

(*-----------qusi-------------*)
and handle_quasi_quote sexpr =  
  match sexpr with
  | ScmNil -> ScmPair(ScmSymbol("quote"), (ScmPair(ScmNil, ScmNil)))
  | ScmChar(x) -> ScmChar(x)
  | ScmString(x) -> ScmString(x)
  | ScmNumber(x) -> ScmNumber(x)
  | ScmBoolean(x) -> ScmBoolean(x)
  | ScmSymbol(x) -> ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol(x), ScmNil))
  | ScmVector(x) -> ScmPair(ScmSymbol("list->vector"), ScmPair(handle_quasi_quote (list_to_proper_list x), ScmNil))
  | ScmPair(ScmSymbol("unquote"), (ScmPair(expr, ScmNil))) -> expr
  | ScmPair(ScmSymbol("unquote-splicing"), ScmPair(expr, ScmNil)) ->
      ScmPair(ScmSymbol("quote"), ScmPair(ScmPair(ScmSymbol("unquote-splicing"), ScmPair(expr, ScmNil)), ScmNil))
  | ScmPair(ScmSymbol("unquote-splicing"), expr) -> raise (X_syntax_error (sexpr, "sexpr structure not recognized"))
  | ScmPair(car, cdr) -> handle_quasi_pair car cdr
  | _ -> sexpr

and handle_quasi_pair car cdr =
  match (car, cdr) with
  | ScmPair(ScmSymbol("unquote-splicing"), ScmPair(sexpr, ScmNil)), cdr ->
        ScmPair(ScmSymbol("append"), ScmPair(sexpr, ScmPair((handle_quasi_quote cdr), ScmNil)))
  | car, ScmPair(ScmSymbol("unquote-splicing"), ScmPair (sexpr, ScmNil)) ->
        ScmPair(ScmSymbol("cons"), ScmPair((handle_quasi_quote car), ScmPair(sexpr, ScmNil)))
  | _, _ -> ScmPair(ScmSymbol("cons"), ScmPair((handle_quasi_quote car), ScmPair((handle_quasi_quote cdr), ScmNil)))
(*-------------- end helpers ----------------*)

end;; 

