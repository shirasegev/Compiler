#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

(*-------------------------------------------*)
let remove_duplicates expr_list =
  let rec run expr_list expr_set =
    match expr_list with
    | expr::exprs ->
        if List.mem expr expr_set
        then run exprs expr_set
        else run exprs (expr_set @ [expr])
    | [] -> expr_set
  in
  run expr_list [];;

let rec find_offset_consts sexpr lst =
  match lst with
  | (e, (offset, _))::rest -> 
      if sexpr_eq e sexpr (* sexpr_eq from tag-parser.ml *)
      then offset
      else find_offset_consts sexpr rest
  | _ -> raise X_this_should_not_happen;;
  
let rec find_offset_fvars name fvars =
  match fvars with
  | (n, offset)::rest -> 
      if n = name (* sexpr_eq from tag-parser.ml *)
      then offset
      else find_offset_fvars name rest
  | _ -> raise X_this_should_not_happen;;
  
let get_size sexpr =
  match sexpr with
  | ScmVoid -> 1
  | ScmNil -> 1
  | ScmBoolean(_) -> 2
  | ScmChar(_) -> 2
  | ScmString(s) -> (String.length s) + 9
  | ScmSymbol(_) -> 9
  | ScmNumber(ScmReal(_)) -> 9
  | ScmNumber(ScmRational(_, _)) -> 17
  | ScmVector(sexpr_list) -> ((List.length sexpr_list) * 8) + 9
  | ScmPair(_, _) -> 17;;

(*-------------------------------------------*)

(*------------- Slides 35 - 39 ---------------
  Constructing the constants-table
    1. Scan the AST (one recursive pass) & collect the sexprs in all Const records
      > The result is a list of sexprs
    2. Convert the list to a set (removing duplicates)
    3. Expand the list to include all sub-constants
      > The list should be sorted topologically
        > Each sub-constant should appear in the list before the const of which it is a part
          For example, (2 3) should appear before (1 2 3)
    4. Convert the resulting list into a set (remove all duplicates, again)
    5. Go over the list, from first to last, and create the constants-table:
      5.1. For each sexpr in the list, create a 3-tuple:
            > The address of the constant sexpr
            > The constant sexpr itself
            > The representation of the constant sexpr as a list of bytes
      5.2. The first constant should start at address zero (0)
      5.3. The constant sexpr is used as a key for looking up constants in the constants-table
      5.4. The representation of a constant is a list of numbers:
            > Each number is a byte, that is, a non-negative integer that is less than 256
      5.5. As you construct the constants-table, you shall need to consult it, in its intermediate state, to look-up the addresses of sub-constants
            > The list of 3-tuples contains all the information needed to lookup & extend the constants-table
-------------------------------------------*)
  let rec make_consts_tbl asts = 
    let extanded_asts = [ScmConst'(ScmVoid); ScmConst'(ScmNil); ScmConst'(ScmBoolean(false)); ScmConst'(ScmBoolean(true))] @ asts in
    let expr_list = List.flatten (List.map extract_consts extanded_asts) in (* stage 1 *)
    let expr_set = remove_duplicates expr_list in                           (* stage 2 *)
    let expanded_list = get_all_sub_constants expr_set in                   (* stage 3 *)
    let expanded_set = remove_duplicates expanded_list in                   (* stage 4 *)
    let consts_tbl = make_tbl expanded_set in
    consts_tbl

  and extract_consts expr =
    match expr with
    | ScmConst'(s) -> [s]
    | ScmVar'(_) | ScmBox'(_) | ScmBoxGet'(_) -> []
    | ScmBoxSet'(_, e) -> extract_consts e
    | ScmIf'(cond, dit, dif) -> (extract_consts cond) @ (extract_consts dit) @ (extract_consts dif)
    | ScmSeq'(expr_list) -> List.flatten (List.map extract_consts expr_list)
    | ScmSet'(_, e) -> extract_consts e
    | ScmDef'(_, e) -> extract_consts e
    | ScmOr'(expr_list) -> List.flatten (List.map extract_consts expr_list)
    | ScmLambdaSimple'(str_lst, body) -> extract_consts body
    | ScmLambdaOpt'(str_lst, opt, body) -> extract_consts body
    | ScmApplic'(proc, expr_list) -> List.flatten (List.map extract_consts ([proc] @ expr_list))
    | ScmApplicTP'(proc, expr_list) -> List.flatten (List.map extract_consts ([proc] @ expr_list))

  and get_all_sub_constants expr_set =
    let rec expand sexrp = 
      (match sexrp with
        | ScmSymbol(s) -> [ScmString(s); sexrp]
        | ScmPair(e, es) -> (expand e) @ (expand es) @ [e; es; sexrp]
        | ScmVector(sexpr_list) -> 
            if sexpr_list = []
            then sexpr_list @ [sexrp]
            else (expand (List.hd (sexpr_list))) @ (get_all_sub_constants (List.tl (sexpr_list))) @ [sexrp]
        | _ -> [sexrp]) in
    let expanded_list = List.flatten (List.map expand expr_set) in
    expanded_list
  
  and make_tbl sexpr_set =
    let first_stage = make_tuple sexpr_set in
    let second_stage = handle_complicated first_stage in
    second_stage

  and make_tuple sexpr_set =
    let offset = ref 0 in
    let curr_offset = ref 0 in
    let tuple sexpr curr_offset = 
      (match sexpr with
      | ScmVoid -> (sexpr, (curr_offset, "db T_VOID"))
      | ScmNil -> (sexpr, (curr_offset, "db T_NIL"))
      | ScmBoolean(false) -> (sexpr, (curr_offset, "db T_BOOL, 0"))
      | ScmBoolean(true) -> (sexpr, (curr_offset, "db T_BOOL, 1"))
      | ScmChar(c) -> (sexpr, (curr_offset, "MAKE_LITERAL_CHAR(" ^ (string_of_int (Char.code c)) ^ ")"))
      | ScmString(s) -> (sexpr, (curr_offset, "MAKE_LITERAL_STRING \"" ^ s ^ "\""))
      | ScmSymbol(s) -> (sexpr, (curr_offset, "WE_ARE_NOT_DONE_YET_WITH_THIS_TUPLE"))
      | ScmNumber(ScmReal(f)) -> (sexpr, (curr_offset, "MAKE_LITERAL_FLOAT(" ^ (string_of_float f) ^ ")"))
      | ScmNumber(ScmRational(n, d)) -> (sexpr, (curr_offset, "MAKE_LITERAL_RATIONAL(" ^ (string_of_int n) ^ ", " ^ (string_of_int d) ^ ")"))
      | ScmVector(sexpr_list) -> (sexpr, (curr_offset, "WE_ARE_NOT_DONE_YET_WITH_THIS_TUPLE"))
      | ScmPair(sexpr1, sexpr2) -> (sexpr, (curr_offset, "WE_ARE_NOT_DONE_YET_WITH_THIS_TUPLE"))
      ) in
      let increase_offset = (fun sexpr -> offset := (!offset + (get_size sexpr))) in
      let create_list sexpr_set =
          List.map (fun sexpr -> curr_offset := !offset; increase_offset sexpr; tuple sexpr !curr_offset) sexpr_set in
      create_list sexpr_set

  and handle_complicated tuple_list =
    let run lst tuple =
      (match tuple with
      | (ScmSymbol(str), (offset, _)) -> (ScmSymbol(str), (offset, "MAKE_LITERAL_SYMBOL(const_tbl + " ^ (string_of_int (find_offset_consts (ScmString(str)) lst)) ^ ")"))
      | (ScmPair(car, cdr), (offset, _)) ->
          (ScmPair(car, cdr), (offset, "MAKE_LITERAL_PAIR(const_tbl + " ^ (string_of_int (find_offset_consts car lst)) ^ ", const_tbl + " ^ (string_of_int (find_offset_consts cdr lst)) ^ ")"))
      | (ScmVector(sexpr_list), (offset, _)) ->
          let str = "MAKE_LITERAL_VECTOR " ^ (String.concat ", " (List.map (fun sexpr -> "const_tbl + " ^ (string_of_int (find_offset_consts sexpr lst))) sexpr_list)) in
          (ScmVector(sexpr_list), (offset, str))
      | _ -> tuple
      )
    in
    List.map (run tuple_list) tuple_list

(*-------------------------------------------*)

let lib_funcs =
  [
    "*"; "+"; "-"; "/"; "<"; "="; ">";
    "append"; "boolean?";  "char->integer"; "char?"; 
    "denominator"; "eq?"; "equal?"; "exact->inexact"; "flonum?"; "gcd";
    "integer?"; "integer->char"; "length"; "list"; "list?"; "make-string"; "map"; "not"; "null?";
    "number?"; "numerator"; "pair?"; "procedure?"; "rational?";
    "string->list"; "string-length"; "string-ref"; "string-set!"; "string?"; "symbol?"; "symbol->string"; "zero?";
    "car"; "cdr"; "cons"; "set-car!"; "set-cdr!"; "apply";
    "cons*"; "fold-left"; "fold-right";
  ];;
  
  let rec make_fvars_tbl asts =
    let fvars_list = List.flatten (List.map extract_fvars asts) in
    let expanded_fvars_list = lib_funcs @ fvars_list in
    let fvars_set = remove_duplicates expanded_fvars_list in
    let fvars_tbl = make_couples fvars_set 0 [] in
    fvars_tbl

  and extract_fvars sexpr =
  (* Make sure Set, Var, Def are really special cases *)
    match sexpr with
    | ScmConst'(_) -> []
    | ScmVar'(VarFree(v)) -> [v]
    | ScmVar'(_) -> []
    | ScmBoxSet'(_, e) -> extract_fvars e
    | ScmIf'(cond, dit, dif) -> (extract_fvars cond) @ (extract_fvars dit) @ (extract_fvars dif)
    | ScmSeq'(expr_list) -> List.flatten (List.map extract_fvars expr_list)
    | ScmSet'(VarFree(v), e) -> v::(extract_fvars e)
    | ScmSet'(_, e) -> extract_fvars e
    | ScmDef'(VarFree(v), e) -> v::(extract_fvars e)
    | ScmDef'(_, e) -> extract_fvars e
    | ScmOr'(expr_list) -> List.flatten (List.map extract_fvars expr_list)
    | ScmLambdaSimple'(str_lst, body) -> extract_fvars body
    | ScmLambdaOpt'(str_lst, opt, body) -> extract_fvars body
    | ScmApplic'(proc, expr_list) -> List.flatten (List.map extract_fvars ([proc] @ expr_list))
    | ScmApplicTP'(proc, expr_list) -> List.flatten (List.map extract_fvars ([proc] @ expr_list))
    | _ -> []

  and make_couples fvar_lst index couples_lst =
    if fvar_lst = []
    then couples_lst
    else make_couples (List.tl fvar_lst) (index + 1) (List.append couples_lst [((List.hd fvar_lst), index)]);;
(*-------------------------------------------*)

let lables_index = ref 0;;
let inc_and_get = (fun _ -> lables_index := (!lables_index + 1); (string_of_int !lables_index));;

let rec generate consts fvars e =
  let rec generate_rec consts fvars e depth =
    match e with
    (* V *)
    | ScmConst'(c) ->
        ";;; ScmConst'\n" ^
        "mov rax, const_tbl+" ^ (string_of_int (find_offset_consts c consts)) ^ "\n" ^
        ";;; End ScmConst'\n"

    (* V *)
    | ScmVar'(v) ->
        (match v with
        | VarFree(name) -> 
          (* get *)
          ";;; ScmVar'(VarFree)\n" ^
            "mov rax, qword [fvar_tbl + (WORD_SIZE * " ^ (string_of_int (find_offset_fvars name fvars)) ^ ")]\n" ^
          ";;; End ScmVar'(VarFree)\n"
        | VarParam(name, minor) -> 
          (* get *)
          ";;; ScmVar'(VarParam)\n" ^
            "mov rax, qword [rbp + WORD_SIZE * (4 + " ^ (string_of_int minor) ^ ")]\n" ^
          ";;; End ScmVar'(VarParam)\n"
        | VarBound(_, major, minor) ->
          (* get *)
          ";;; ScmVar'(VarBound)\n" ^
            "mov rax, qword [rbp + WORD_SIZE * 2]\n" ^
            "mov rax, qword [rax + WORD_SIZE * " ^ (string_of_int major) ^ "]\n" ^
            "mov rax, qword [rax + WORD_SIZE * " ^ (string_of_int minor) ^ "]\n" ^
          ";;; End ScmVar'(VarBound)\n"
        )
    
    (* V *)
    | ScmBox'(v) ->
      ";;; ScmBox'\n" ^
        (generate_rec consts fvars (ScmVar'(v)) depth) ^
        "MALLOC rbx, WORD_SIZE\n" ^
        "mov qword [rbx], rax\n" ^ 
        "mov rax, rbx\n" ^
      ";;; End ScmBox'\n"
    | ScmBoxGet'(v) -> 
      ";;; ScmBoxGet'\n" ^
        (generate_rec consts fvars (ScmVar'(v)) depth) ^
        "\nmov rax, qword [rax]\n" ^
      ";;; End ScmBoxGet'\n"
    | ScmBoxSet'(v, expr) ->
      ";;; ScmBoxSet'\n" ^
        (generate_rec consts fvars expr depth) ^
        "\npush rax\n" ^
        (generate_rec consts fvars (ScmVar'(v)) depth) ^
        "\npop qword [rax]" ^
        "\nmov rax, SOB_VOID_ADDRESS\n" ^
      ";;; End ScmBoxSet'\n"
    
    (* V *)
    | ScmIf'(cond, dit, dif) ->
        let index = inc_and_get() in
        let lelse = "Lelse" ^ index in
        let lexit = "Lexit" ^ index in

      ";;; ScmIf'\n" ^
        (generate_rec consts fvars cond depth) ^
        "\ncmp rax, SOB_FALSE_ADDRESS\n" ^
        "je " ^ lelse ^ "\n" ^
        (generate_rec consts fvars dit depth) ^
        "\njmp " ^ lexit ^ "\n" ^
        lelse ^ ":\n" ^
        (generate_rec consts fvars dif depth) ^
        "\n" ^ lexit ^ ":\n" ^
      ";;; End ScmIf'\n"
        
    (* V *)
    | ScmSeq'(expr_list) -> 
      ";;; ScmSeq'\n" ^
        (String.concat ("\n") (List.map (fun expr -> generate_rec consts fvars expr depth) expr_list)) ^ "\n" ^
      ";;; End ScmSeq'\n"
        
    (* V *)
    | ScmSet'(v, expr) ->
        (match v with
        | VarFree(name) -> 
        ";;; ScmSet'(VarFree)\n" ^
            (generate_rec consts fvars expr depth) ^
            "\nmov qword [fvar_tbl + WORD_SIZE * " ^ (string_of_int (find_offset_fvars name fvars)) ^ "], rax\n" ^
            "mov rax, SOB_VOID_ADDRESS\n" ^
          ";;; End ScmSet'(VarFree)\n"
        | VarParam(_, minor) -> 
        ";;; ScmSet'(VarParam)\n" ^
            (generate_rec consts fvars expr depth) ^
            "\nmov qword [rbp + WORD_SIZE * (4 + " ^ (string_of_int minor) ^ ")], rax\n" ^
            "mov rax, SOB_VOID_ADDRESS\n" ^
          ";;; End ScmSet'(VarParam)\n"
        | VarBound(_, major, minor) ->
          ";;; ScmSet'(VarBound)\n" ^
            (generate_rec consts fvars expr depth) ^
            "\nmov rbx, qword [rbp + WORD_SIZE * 2]\n" ^
            "mov rbx, qword [rbp + WORD_SIZE * " ^ (string_of_int major) ^ "]\n" ^
            "mov qword [rbx + WORD_SIZE * " ^ (string_of_int minor) ^ "], rax\n" ^
            "mov rax, SOB_VOID_ADDRESS\n" ^
          ";;; End ScmSet'(VarBound)\n"
        )

    (* V *)
    | ScmDef'(VarFree(name), expr) -> 
      ";;; ScmDef'\n" ^
        (generate_rec consts fvars expr depth) ^
        "\nmov qword [fvar_tbl + WORD_SIZE * " ^ (string_of_int (find_offset_fvars name fvars)) ^ "], rax\n" ^
        "mov rax, SOB_VOID_ADDRESS\n" ^
      ";;; End ScmDef\n"

    (* V *)
    | ScmOr'(expr_list) ->
        let lexit = "Lexit" ^ inc_and_get() in

      ";;; ScmOr'\n" ^
        (String.concat
          ("\ncmp rax, SOB_FALSE_ADDRESS\n" ^
          "jne " ^ lexit ^ "\n")
          (List.map (fun expr -> generate_rec consts fvars expr depth) expr_list)
        ) ^ ("\n" ^ lexit ^ ":\n") ^
      ";;; End ScmOr\n"
  
    | ScmLambdaSimple'(str_lst, body) ->
        let index = inc_and_get() in
        let lcont = "Lcont" ^ index in
        let lcode = "Lcode" ^ index in

      ";;; ScmLambdaSimple\n" ^
        (* create ExtEnv *)
        (extend_env depth index) ^

        (* Allocate closure Object *)
        "\nMAKE_CLOSURE(rax, rbx, " ^ lcode ^ ")\n" ^

        (* Closure -> Env := ExtEnv
        Closure -> Code := Lcode *)
        "jmp " ^ lcont ^ "\n" ^

        (* Closure body *)
        lcode ^ ":\n" ^
        "push rbp\n" ^
        "mov rbp, rsp\n" ^
        (generate_rec consts fvars body (depth + 1)) ^
        "\nleave" ^
        "\nret\n" ^

        lcont ^ ":\n" ^
      ";;; End ScmLambdaSimple\n"

    | ScmLambdaOpt'(str_lst, opt, body) ->
        let index = inc_and_get() in
        let lcont = "Lcont" ^ index in
        let lcode = "Lcode" ^ index in
    
      ";;; ScmLambdaOpt\n" ^
        (* create ExtEnv *)
        (extend_env depth index) ^
    
        (* Allocate closure Object *)
        "\nMAKE_CLOSURE(rax, rbx, " ^ lcode ^ ")\n" ^
    
        (* Closure -> Env := ExtEnv
        Closure -> Code := Lcode *)
        "jmp " ^ lcont ^ "\n" ^
    
        (* Closure body *)
        lcode ^ ":\n" ^
    
        "\npush rbp\n" ^
        "mov rbp, rsp\n" ^
        (* adjust stack for opt args *)
        (adjust_stack depth index str_lst) ^
        (generate_rec consts fvars body (depth + 1)) ^
        "\nleave\n" ^
        "ret\n\n" ^
    
        lcont ^ ":\n" ^
      ";;; End ScmLambdaOpt\n"

    | ScmApplic'(proc, expr_list) ->
      ";;; APPLIC\n" ^
        "push SOB_NIL_ADDRESS\n" ^ (* FOR MAGIC! *)
        (
            if expr_list = []
            then ""
            else 
            ((String.concat
              ("push rax\n")
              (List.map (fun expr -> generate_rec consts fvars expr depth) (List.rev expr_list))
            ) ^ ("push rax\n"))
        ) ^
        "push " ^ (string_of_int (List.length expr_list)) ^ "\n" ^
        (generate_rec consts fvars proc depth) ^
        "\nCLOSURE_ENV rbx, rax\n" ^
        "push rbx\n" ^
        "CLOSURE_CODE rbx, rax\n" ^
        "call rbx\n\n" ^

        "add rsp, WORD_SIZE ; pop env\n" ^
        "pop rbx ; pop arg count\n" ^

        "lea rsp, [rsp + (WORD_SIZE * rbx)] ; pop args\n" ^

        "add rsp, WORD_SIZE ; clean MAGIC!\n" ^
      ";;; End APPLIC\n"

    | ScmApplicTP'(proc, expr_list) ->
        let n = List.length expr_list in

      ";;; APPLICTP\n" ^
        "push SOB_NIL_ADDRESS\n" ^

        (
            if expr_list = []
            then ""
            else 
            ((String.concat
              ("push rax\n")
              (List.map (fun expr -> generate_rec consts fvars expr depth) (List.rev expr_list))
            ) ^ ("push rax\n"))
        ) ^
        "push " ^ (string_of_int n) ^ "\n" ^
        (generate_rec consts fvars proc depth) ^

        "\nCLOSURE_ENV rbx, rax\n" ^
        "push rbx\n" ^
        "push qword[rbp + WORD_SIZE] ; prev ret address\n\n" ^

        "SHIFT_FRAME " ^ (string_of_int (n + 4)) ^ "\n" ^ (* +4 -> MAGIC! *)
        "CLOSURE_CODE rbx, rax\n" ^
        
        "jmp rbx\n" ^
      ";;; End APPLICTP\n"

    | _ -> "COMPILER"
  in
  generate_rec consts fvars e 0

  and extend_env depth index =
    let copy_params_loop = "copy_params_loop" ^ index in
    let end_copy_params_loop = "end_copy_params_loop" ^ index in
    let copy_envs_loop = "copy_envs_loop" ^ index in
    let end_copy_envs_loop = "end_copy_envs_loop" ^ index in
  
    "mov rax, " ^ string_of_int (depth + 1) ^ "\n" ^
    "shl rax, 3\n" ^ (* 8 *)
    "MALLOC rbx, rax\n" ^
    "mov rcx, WORD_SIZE\n" ^
    "add rcx, rbx\n" ^
    "mov rdx, qword[rbp + WORD_SIZE * 2]\n\n" ^
  
    "mov r10, 0\n" ^
    copy_envs_loop ^ ":\n" ^
      "cmp r10, " ^ (string_of_int depth) ^ "\n" ^
      "je " ^ end_copy_envs_loop ^ "\n" ^
      "lea rdi, [rdx + WORD_SIZE * r10]\n" ^
      "mov r11, [rdi]\n" ^
      "lea rsi, [rcx + WORD_SIZE * r10]\n" ^
      "mov [rsi], r11\n" ^
      "inc r10\n" ^
      "jmp " ^ copy_envs_loop ^ "\n" ^
      
    end_copy_envs_loop ^ ":\n" ^
      "sub rcx, WORD_SIZE\n" ^
      "mov rdx, 0\n" ^
      "add rdx, PARAM_COUNT\n" ^
      "inc rdx\n" ^
      "cmp rdx, 0\n" ^
      "je " ^ end_copy_params_loop ^ "\n" ^
  
    "shl rdx, 3\n" ^
    "MALLOC r11, rdx\n" ^
    "mov [rcx], r11\n" ^
    "mov rcx, r11\n" ^
  
    "sar rdx, 3\n" ^
    "mov r10, 0\n" ^
    copy_params_loop ^ ":\n" ^
      "cmp r10, rdx\n" ^
      "je " ^ end_copy_params_loop ^ "\n" ^
      "lea rdi, [rbp + WORD_SIZE * (4 + r10)]\n" ^
      "lea rsi, [rcx + WORD_SIZE * r10]\n" ^
      "mov r11, [rdi]\n" ^
      "mov [rsi], r11\n" ^
      "inc r10\n" ^
      "jmp " ^ copy_params_loop ^ "\n\n" ^
    
    end_copy_params_loop ^ ":\n"

  and adjust_stack depth index params = 
    let n = string_of_int (List.length params) in
    let adjustment_body = "adjustment_body" ^ index in
    let shift_loop = "shift_loop" ^ index in
    let end_shift_loop = "end_shift_loop" ^ index in
    let end_adjustment = "end_adjustment" ^ index in

    "mov rdx, PARAM_COUNT\n" ^
    "add rdx, 3\n" ^
    "mov r10, PARAM_COUNT\n" ^
    "mov PARAM_COUNT, " ^ n ^ "\n" ^
    "sub r10, PARAM_COUNT\n" ^ 
    "lea rsi, [rbp + WORD_SIZE * rdx]\n\n" ^

    adjustment_body ^ ":\n" ^
      "cmp r10, 0\n" ^
      "je " ^ end_adjustment ^ "\n" ^
      "mov rdi, [rsi]\n" ^
      "add rsi, WORD_SIZE\n" ^
      "mov rcx, [rsi]\n" ^
      "MAKE_PAIR(rax, rdi, rcx)\n" ^
      "mov qword[rsi], rax\n" ^
      "sub rsi, WORD_SIZE\n\n" ^

      "mov rcx, 0\n" ^
      "mov rbx, rsi\n" ^
      shift_loop ^ ":\n" ^
        "cmp rcx, rdx\n" ^
        "je " ^ end_shift_loop ^ "\n" ^
        "mov r11, rbx\n" ^
        "sub r11, WORD_SIZE\n" ^
        "mov r12, qword[r11]\n" ^
        "mov qword[rbx], r12\n" ^
        "mov rbx, r11\n" ^
        "inc rcx\n" ^
        "jmp " ^ shift_loop ^ "\n\n" ^
      
      end_shift_loop ^ ":\n" ^
        "add rbp, WORD_SIZE\n" ^
        "mov rsp, rbp\n" ^
        "dec rdx\n" ^
        "dec r10\n" ^
        "jmp " ^ adjustment_body ^ "\n" ^
    end_adjustment ^ ":\n\n";;

(*-------------------------------------------*)

end;;
