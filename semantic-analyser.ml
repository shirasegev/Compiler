(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe =
   let rec run pe params env =
      (*-------------------------------------------*)
      match pe with
      | ScmConst(sexpr) -> ScmConst'(sexpr)
      | ScmVar(v) -> ScmVar'(tag_lexical_address_for_var v params env)
      | ScmIf(q, t, e) -> ScmIf'(run q params env, run t params env, run e params env)
      | ScmSeq(expr_list) -> ScmSeq'(List.map (fun expr -> run expr params env) expr_list)
      | ScmSet(ScmVar(v), e) -> ScmSet'(tag_lexical_address_for_var v params env, run e params env)
      | ScmDef(ScmVar(v), e) -> ScmDef'(tag_lexical_address_for_var v params env, run e params env)
      | ScmOr(expr_list) -> ScmOr'(List.map (fun expr -> run expr params env) expr_list)
      | ScmLambdaSimple(str_lst, body) -> ScmLambdaSimple'(str_lst, run body str_lst (params::env))
      | ScmLambdaOpt(str_lst, opt, body) -> ScmLambdaOpt'(str_lst, opt, run body (str_lst@[opt]) (params::env))
      | ScmApplic(expr, expr_list) -> ScmApplic'(run expr params env, List.map (fun expr -> run expr params env) expr_list)
      | _ -> raise X_this_should_not_happen
      (*-------------------------------------------*)
   in 
   run pe [] [];;

  (* it's like hd::tl, but reversed. example: input: [1;2;3] -> output: ([1;2],3) *)
  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  
  (* run this second! *)
  let annotate_tail_calls pe =
    let rec run pe in_tail =
      (*-------------------------------------------*)
      match pe, in_tail with
      | ScmConst'(sexpr), _ -> ScmConst'(sexpr)
      | ScmVar'(v), _ -> ScmVar'(v)
      | ScmIf'(q, t, e), _ -> ScmIf'(run q false, run t in_tail, run e in_tail)
      | ScmSeq'(expr_list), _ -> ScmSeq'(annotate_tail_list expr_list)
      | ScmSet'(v, e), _ -> ScmSet'(v, run e false)
      | ScmDef'(v, e), _ -> ScmDef'(v, run e false)
      | ScmOr'(expr_list), _ -> ScmOr'(annotate_tail_list expr_list)
      | ScmLambdaSimple'(str_lst, body), _ -> ScmLambdaSimple'(str_lst, run body true)
      | ScmLambdaOpt'(str_lst, opt, body), _ -> ScmLambdaOpt'(str_lst, opt, run body true)
      | ScmApplic'(expr, expr_list), false -> ScmApplic'(run expr false, List.map (fun expr -> run expr false) expr_list)
      | ScmApplic'(expr, expr_list), true -> ScmApplicTP'(run expr false, List.map (fun expr -> run expr false) expr_list)
      | _, _ -> raise X_this_should_not_happen

  and annotate_tail_list expr_list =
    (List.mapi (fun i expr -> 
                  if (i = (List.length expr_list - 1))
                  then (run expr true)
                  else (run expr false))
    expr_list)
  (*-------------------------------------------*)
  in 
  run pe false;;

  (* boxing *)
(*-------------------------------------------*)
  let index_of key lst =
    let rec run key lst index =
      match lst with
      | [] -> -1
      | _ -> if (List.hd lst) = key then index else run key (List.tl lst) (index + 1)
    in
    run key lst 0;;

  let var_eq var1 var2 =
    match var1 with
    | VarFree(x) -> x = var2
    | VarParam(name, _) -> name = var2
    | VarBound(name, _, _) -> name = var2
(*-------------------------------------------*)

  let find_reads name enclosing_lambda expr =
  (*-------------------------------------------*)
    let rec run enclosing_lambda expr =
      match expr with
      | ScmConst'(_) | ScmVar'(VarFree(_)) | ScmBox'(_) | ScmBoxGet'(_) -> []
      | ScmVar'(VarParam (name', minor)) -> if name = name' then [(VarParam (name', minor), enclosing_lambda)] else []
      | ScmVar'(VarBound (name', minor, major)) -> if name = name' then [(VarBound (name', minor, major), enclosing_lambda)] else []
      | ScmBoxSet'(_, expr) -> run enclosing_lambda expr
      | ScmIf'(q, t, e) -> (run enclosing_lambda q) @ (run enclosing_lambda t) @ (run enclosing_lambda e)
      | ScmSeq'(expr_list) | ScmOr'(expr_list) -> List.fold_left(fun res expr -> res @ (run enclosing_lambda expr)) [] expr_list
      | ScmSet'(_, expr) | ScmDef'(_, expr) -> run enclosing_lambda expr
      | ScmApplic'(expr, expr_list) | ScmApplicTP'(expr, expr_list) ->
          (run enclosing_lambda expr) @ (List.fold_left (fun res expr -> res @ (run enclosing_lambda expr)) [] expr_list)
      | ScmLambdaSimple'(str_lst, body) -> if (List.mem name str_lst) then [] else run expr body
      | ScmLambdaOpt'(str_lst, opt, body) -> if ((List.mem name str_lst) || name = opt) then [] else run expr body
    in
    run enclosing_lambda expr

  let rec find_writes name enclosing_lambda expr =
    let rec run enclosing_lambda expr =
      match expr with
      | ScmConst'(_) | ScmVar'(_) | ScmBox'(_) | ScmBoxGet'(_) | ScmBoxSet'(_, _) -> []
      | ScmIf'(q, t, e) -> (run enclosing_lambda q) @ (run enclosing_lambda t) @ (run enclosing_lambda e)
      | ScmSeq'(expr_list) | ScmOr'(expr_list) -> List.fold_left (fun res expr -> res @ (run enclosing_lambda expr)) [] expr_list
      | ScmSet'(v, expr) -> find_writes_set name enclosing_lambda v expr
      | ScmDef'(v, expr) -> run enclosing_lambda expr
      | ScmApplic'(expr, expr_list) | ScmApplicTP'(expr, expr_list) ->
          (run enclosing_lambda expr) @ (List.fold_left (fun res expr -> res @ (run enclosing_lambda expr)) [] expr_list)
      | ScmLambdaSimple'(str_lst, body) -> if (List.mem name str_lst) then [] else run expr body
      | ScmLambdaOpt'(str_lst, opt, body) -> if (List.mem name str_lst) || (name = opt) then [] else run expr body

    and find_writes_set name enclosing_lambda v expr =
      match v with
      | VarParam (name', minor) ->
          if name' = name 
          then [(VarParam(name', minor), enclosing_lambda)] @ (run enclosing_lambda expr)
          else [] @ (run enclosing_lambda expr)
      | VarBound (name', minor, major) ->
          if name' = name
          then [(VarBound(name', minor, major), enclosing_lambda)] @ (run enclosing_lambda expr)
          else [] @ (run enclosing_lambda expr)
      | VarFree(x) -> [] @ (run enclosing_lambda expr)
    in
    run enclosing_lambda expr

  (*-------------------------------------------*)
  let rec box_set expr =
    match expr with
    | ScmConst'(_) | ScmVar'(_) | ScmBox'(_) | ScmBoxGet'(_) -> expr
    | ScmBoxSet'(v, expr) -> ScmBoxSet'(v, box_set expr)
    | ScmIf'(q, t, e) -> ScmIf'(box_set q, box_set t, box_set e)
    | ScmSeq'(expr_list) -> ScmSeq'(List.map box_set expr_list)
    | ScmSet'(v, e) -> ScmSet'(v, box_set e)
    | ScmDef'(v, e) -> ScmDef'(v, box_set e)
    | ScmOr'(expr_list) -> ScmOr'(List.map box_set expr_list)
    | ScmLambdaSimple'(str_lst, body) -> box_set_lambda_simple str_lst body expr   
    | ScmLambdaOpt'(str_lst, opt, body) -> box_set_lambda_opt str_lst opt body expr
    | ScmApplic'(expr, expr_list) -> ScmApplic'(box_set expr, List.map box_set expr_list)
    | ScmApplicTP'(expr, expr_list) -> ScmApplicTP'(box_set expr, List.map box_set expr_list)

  and box_set_lambda_simple str_lst body expr =
    let box_these = List.filter (fun p -> should_box_var p expr body) str_lst in
    let new_body = fun body -> List.fold_right (box_sets_and_gets str_lst) box_these body in
    ScmLambdaSimple'(str_lst, (box_set (new_body body)))

  and box_set_lambda_opt str_lst opt body expr =
    let params = str_lst @ [opt] in
    let box_these = List.filter (fun p -> should_box_var p expr body) params in
    let new_body = fun body -> List.fold_right (box_sets_and_gets params) box_these body in
    ScmLambdaOpt'(str_lst, opt, (box_set (new_body body)))

  and should_box_var name enclosing_lambda expr =
    let reads = find_reads name enclosing_lambda expr in
    let writes = find_writes name enclosing_lambda expr in
    let cartesian_product = (List.rev (List.fold_left (fun x a -> List.fold_left(fun y b -> (a, b) :: y) x writes) [] reads)) in
    let rec run expr =
      match expr with
      | [] -> false
      | ((VarParam(_, _), _), (VarParam(_, _), _)) :: rest -> run rest
      | ((VarParam(_, _), _), (VarBound(_, _, _), _)) :: rest -> true
      | ((VarBound(_, _, _), _), (VarParam(_, _), _)) :: rest -> true
      | ((VarBound(n1, maj1, min1), lam1), (VarBound(n2, maj2, min2), lam2)) :: rest ->
          if ((maj1 = 0) && (0 < maj2)) || ((maj1 > 0) && (0 = maj2))
              || (((maj1 = 0) && (0 = maj2)) && ((inside_eq lam1 lam2) || (inside_eq lam2 lam1)))
              || (((0 < maj1) && (0 < maj2)) && (handle_bound_bound enclosing_lambda lam1 lam2))
          then run rest else true
      | _ :: rest -> run rest
    in
    run cartesian_product
    
    and handle_bound_bound enclosing_lambda lam1 lam2 =
      match enclosing_lambda with
      | ScmLambdaSimple'(str_list, body) -> should_box_lambda lam1 lam2 body
      | ScmLambdaOpt'(str_list, opt, body) -> should_box_lambda lam1 lam2 body
      | _ -> false

    and should_box_lambda lam1 lam2 body =
      match body with
      | ScmSeq'(expr_list) -> List.fold_left (fun b1 b2 -> b1 || b2) false (List.map (fun ex -> check_lambdas lam1 lam2 ex) expr_list)
      | _ -> check_lambdas lam1 lam2 body

    and check_lambdas lam1 lam2 body =
      match body with
      | ScmLambdaSimple'(str_list, ScmSeq'(expr_list)) ->
            List.fold_left (fun b1 b2 -> b1 || b2) false (List.map (fun ex -> (inside_eq ex lam1) && (inside_eq ex lam2)) expr_list)
      | ScmLambdaSimple'(str_list, body) -> (inside_eq body lam1) && (inside_eq body lam2)
      | ScmLambdaOpt'(str_list, opt, ScmSeq'(expr_list)) ->
            List.fold_left (fun b1 b2 -> b1 || b2) false (List.map (fun ex -> (inside_eq ex lam1) && (inside_eq ex lam2)) expr_list)
      | ScmLambdaOpt'(str_list, opt, body) -> 
          (inside_eq body lam1) && (inside_eq body lam2)
      | _ -> false

  and inside_eq lam1 lam2 =
    match lam1 with
    | ScmConst'(_) | ScmVar'(_) | ScmBox'(_) | ScmBoxGet'(_) -> false
    | ScmBoxSet'(_, expr) -> inside_eq expr lam2
    | ScmIf'(q, t, e) -> (inside_eq q lam2) || (inside_eq t lam2) || (inside_eq e lam2)
    | ScmSeq'(expr_list) -> (ormap (fun expr -> inside_eq expr lam2) expr_list)
    | ScmSet'(_, expr) -> inside_eq expr lam2
    | ScmDef'(_, expr) -> inside_eq expr lam2
    | ScmOr'(expr_list) -> (ormap (fun expr -> inside_eq expr lam2) expr_list)
    | ScmLambdaSimple'(str_lst, body) -> (lam1 == lam2) || (inside_eq body lam2)
    | ScmLambdaOpt'(str_lst, opt, body) -> (lam1 == lam2) || (inside_eq body lam2)
    | ScmApplic'(expr, expr_list) -> (inside_eq expr lam2) || (ormap (fun arg -> inside_eq arg lam2) expr_list)
    | ScmApplicTP'(expr, expr_list) -> (inside_eq expr lam2) || (ormap (fun arg -> inside_eq arg lam2) expr_list)

  and box_sets_and_gets params name body =
    let minor = index_of name params in
    let set_box_expr = ScmSet'(VarParam(name, minor), ScmBox'(VarParam(name, minor))) in
    let compute body =
      match body with
      | ScmSeq'(expr_list) -> ScmSeq'(set_box_expr :: expr_list)
      | _ -> ScmSeq'([set_box_expr; body])
    in
    box_writes name (box_reads name (compute body))

  and box_reads var expr =
    match expr with
    | ScmVar'(v) -> if (var_eq v var) then ScmBoxGet'(v) else expr
    | ScmBoxSet'(v, expr) -> ScmBoxSet'(v, box_reads var expr)
    | ScmIf'(q, t, e) -> ScmIf'(box_reads var q, box_reads var t, box_reads var e)
    | ScmSeq'(expr_list) -> ScmSeq'(List.map (box_reads var) expr_list)
    | ScmOr'(expr_list) -> ScmOr'(List.map (box_reads var) expr_list)
    | ScmSet'(v, expr) -> ScmSet'(v, box_reads var expr)
    | ScmDef'(v, expr) -> ScmDef'(v, box_reads var expr)
    | ScmApplic'(expr, expr_list) -> ScmApplic'(box_reads var expr, (List.map (box_reads var) expr_list))
    | ScmApplicTP'(expr, expr_list) -> ScmApplicTP'(box_reads var expr, (List.map (box_reads var) expr_list))
    | ScmLambdaSimple'(str_list, body) -> box_lambda_simple var expr str_list body box_reads
    | ScmLambdaOpt'(str_list, opt, body) -> box_lambda_opt var expr str_list opt body box_reads
    | _ -> expr

  and box_writes var expr =
    match expr with
    | ScmBoxSet'(v, expr) -> ScmBoxSet'(v, box_writes var expr)
    | ScmIf'(q, t, e) -> ScmIf'(box_writes var q, box_writes var t, box_writes var e)
    | ScmSeq'(expr_list) -> ScmSeq'(List.map (box_writes var) expr_list)
    | ScmSet'(v, e) -> (match e with
                        | ScmBox'(x) -> expr
                        | _ -> if (var_eq v var) then ScmBoxSet'(v, box_writes var e) else ScmSet'(v, box_writes var e))
    | ScmDef'(v, expr) -> ScmDef'(v, box_writes var expr)
    | ScmOr'(expr_list) -> ScmOr'(List.map (box_writes var) expr_list)
    | ScmApplic'(expr, expr_list) -> ScmApplic'(box_writes var expr, (List.map (box_writes var) expr_list))
    | ScmApplicTP'(expr, expr_list) -> ScmApplicTP'(box_writes var expr, (List.map (box_writes var) expr_list))
    | ScmLambdaSimple'(str_list, body) -> box_lambda_simple var expr str_list body box_writes
    | ScmLambdaOpt'(str_list, opt, body) -> box_lambda_opt var expr str_list opt body box_writes
    | _ -> expr

  and box_lambda_simple var expr str_list body f =
    if ((index_of var str_list) = -1)
    then ScmLambdaSimple'(str_list, f var body)
    else expr

  and box_lambda_opt var expr str_list opt body f =
    if (index_of var (opt :: str_list) = -1)
    then ScmLambdaOpt'(str_list, opt, f var body)
    else expr
(*-------------------------------------------*)

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)
