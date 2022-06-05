(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

module type READER = sig
    val nt_sexpr : sexpr PC.parser
end;; (* end of READER signature *)

module Reader : READER = struct
open PC;;

let unitify nt = pack nt (fun _ -> ());;
let maybeify nt none_value =
  let nt1 = pack (maybe nt) (function
                | None -> none_value
                | Some(x) -> x) in
  nt1;;

(*Came with the code:*)
let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str
and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str

and nt_line_comment str =
  let nt_end = disj (unitify (char '\n')) (unitify nt_end_of_input) in
  let nt1 = char ';' in
  let nt2 = diff nt_any nt_end in
  let nt2 = star nt2 in
  let nt1 = caten nt1 (caten nt2 nt_end) in
  let nt1 = unitify nt1 in
  nt1 str

and nt_paired_comment str =
  let nt1 = disj_list [unitify nt_char;
                        unitify nt_string;
                        nt_comment] in
  let nt2 = diff nt_any (disj nt1 (unitify (one_of "{}"))) in
  let nt2 = disj (unitify nt2) nt1 in
  let nt2 = star nt2 in
  let nt1 = unitify (caten (char '{') (caten nt2 (char '}'))) in
  nt1 str

and nt_sexpr_comment str =
  let nt1 = unitify (caten (word "#;") nt_sexpr) in
  nt1 str

(*Came with the code:*)
and nt_comment str =
  disj_list
    [nt_line_comment;
     nt_paired_comment;
     nt_sexpr_comment
     ] str
and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str
and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1

and nt_digit str =
  let nt1 = range '0' '9' in
  let nt1 = pack nt1 (let delta = int_of_char '0' in
            fun ch -> (int_of_char ch) - delta) in
  nt1 str
and nt_is_positive_number str =
  let nt1 = pack (char '+') (fun _ -> true) in
  let nt2 = pack (char '-') (fun _ -> false) in
  let nt1 = disj nt1 nt2 in
  let nt1 = maybe nt1 in
  let nt1 = pack nt1 (function
                | None -> true
                | Some b -> b) in
  nt1 str
and nt_nat str = 
  let nt1 = plus nt_digit in
  let nt1 = pack nt1 (fun x -> List.fold_left
              (fun num digit -> 10 * num + digit)
              0
              x) in
  nt1 str

and nt_int str =
  let nt1 = plus nt_digit in
  let nt1 = pack nt1
              (fun digits ->
                List.fold_left
                (fun num digit -> 10 * num + digit)
                0
              digits) in
  let nt1 = caten nt_is_positive_number nt1 in
  let nt1 = pack nt1
              (fun (is_positive, n) ->
                if is_positive then n else -n) in
  nt1 str

and nt_frac str =
  let nt1 = only_if nt_nat (fun n -> n > 0) in
  let nt2 = caten nt_int (caten (char '/') nt1) in
  let nt2 = pack nt2
              (fun (num, (_, nat)) ->
              let d = gcd num nat in
              if d > 0 then ScmRational (num / d, nat/ d)
              else ScmRational (num / (-1 * d), nat/ (-1 * d))) in
  nt2 str

and nt_integer_part str =
  let nt1 = plus nt_digit in
  let nt1 = pack nt1
              (fun digits ->
              List.fold_left
              (fun num digit ->
              10.0 *. num +. (float_of_int digit))
              0.0
              digits) in
  nt1 str

and nt_mantissa str =
  let nt1 = plus nt_digit in
  let nt1 = pack nt1
              (fun digits ->
                List.fold_right
                  (fun digit num ->
                    ((float_of_int digit) +. num) /. 10.0)
                    digits
                    0.0) in
  nt1 str

and nt_exponent str =
  let nt1 =
    disj_list [unitify (char_ci 'e');
               unitify (word "*10^");
               unitify (word "*10**")] in
  let nt1 = caten nt1 nt_int in
  let nt1 = pack nt1
              (fun (_, n) ->
                Float.pow 10.0 (float_of_int n)) in
  nt1 str

and nt_float str =
  let nt1 = nt_is_positive_number in

  (* float-a*)
  let nt2 = nt_integer_part in
  let nt3 = char '.' in
  let nt4 = maybeify nt_mantissa 0.0 in
  let nt5 = maybeify nt_exponent 1.0 in
  let nt2 = caten nt2 (caten nt3 (caten nt4 nt5)) in
  let nt2 = pack nt2
              (fun (int_part, (_, (mant, mult))) ->
                (int_part +. mant) *. mult) in
  
  (* float-b*)
  let nt3 = char '.' in
  let nt4 = nt_mantissa in
  let nt5 = maybeify nt_exponent 1.0 in
  let nt3 = caten nt3 (caten nt4 nt5) in
  let nt3 = pack nt3
              (fun (_, (mant, mult)) ->
                mant *. mult) in
  
  (* float-c*)
  let nt4 = caten nt_integer_part nt_exponent in
  let nt4 = pack nt4
              (fun (int_part, mult) ->
                int_part *. mult) in

  let nt2 = disj nt2 (disj nt3 nt4) in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1
              (fun (is_positive, x) ->
                if is_positive then x else (-. x)) in
  let nt1 = pack nt1 (fun x -> ScmReal (x)) in
  nt1 str

(*Came with the code:*)
and nt_number str =
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str

and nt_boolean str = 
  let nt1 = pack (word_ci "#f") (fun _ -> false) in
  let nt2 = pack (word_ci "#t") (fun _ -> true) in
  let nt1 = disj nt1 nt2 in
  let nt1 = pack nt1 (fun b -> ScmBoolean b) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str

and char_prefix str =
  let nt1 = word "#\\" in
  nt1 str

and nt_char_simple str =
  let nt1 = range (char_of_int 33) (char_of_int 127) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str

and make_named_char char_name ch =
  disj_list [pack (word_ci "newline") (fun _ -> (char_of_int 10));
             pack (word_ci "nul") (fun _ -> (char_of_int 0));
             pack (word_ci "return") (fun _ -> (char_of_int 13));
             pack (word_ci "tab") (fun _ -> (char_of_int 9));
             pack (word_ci "page") (fun _ -> (char_of_int 12));
             pack (word_ci "space") (fun _ -> (char_of_int 32))]

(*Came with the code:*)
and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "nul" '\000');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t')] in
  nt1 str

and nt_hexadecimal_char str = 
  let hex = pack (char_ci 'x') (fun x -> x) in
  let r1 = range 'a' 'f' in
  let r2 = range '0' '9' in
  let ranges = plus (disj r1 r2) in
  pack (caten hex ranges)
            (fun (l,r) -> 
                (char_of_int (int_of_string (list_to_string ('0' :: 'x' :: r))))) str

and nt_char str =
  (pack (pack (pack (caten char_prefix (disj_list [nt_char_simple; nt_hexadecimal_char; nt_char_named]))  
  (fun (h,x) -> h@[x]))(fun lst -> List.hd (List.tl (List.tl lst)))) (fun r -> ScmChar r))
  str

and nt_symbol_char str =
  disj_list 
    [(range_ci 'a' 'z');
     (range '0' '9');
     (one_of "!$^*-_=+<>?/:")] str

(*Came with the code:*)
and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str

and nt_string str =
  let q = word "\"" in
  let str_char = disj_list [nt_string_meta_char; nt_string_hex_char; nt_string_literal_char] in
  let str_char = plus str_char in
  let str_char = pack str_char (fun s -> ScmString (list_to_string s)) in
  let global_string = star (disj str_char nt_string_interpolated) in

  let nt1 = (caten global_string q) in
  let nt1 = pack nt1 (fun (x, _)-> x) in
  let nt2 = caten q nt1 in
  let nt2 = pack nt2 (fun (_, x)-> x) in
  let nt1 = pack nt2
   (fun sexps ->
    match sexps with
    | [] -> ScmString ""
    | car :: [] -> car
    | car :: cdr -> ScmPair(ScmSymbol "string-append", 
                    (List.fold_right 
                    (fun x y -> ScmPair(x, y)) 
                    sexps ScmNil))) in
  nt1 str

and nt_string_literal_char str =
  disj_list [range (char_of_int 0) (char_of_int 33);
             range (char_of_int 35) (char_of_int 91);
             range (char_of_int 93) (char_of_int 125);
             range (char_of_int 127) (char_of_int 127)] str

and nt_string_hex_char str =
  let backs = pack (char '\\') (fun s-> [s]) in
  let hex = pack (char_ci 'x') (fun s-> [s]) in
  let nt1 = caten backs hex in
  let r1 = range 'a' 'f' in
  let r2 = range '0' '9' in
  let ranges = plus (disj r1 r2) in
  let term = pack (char ';') (fun s -> [s]) in
  pack (caten (caten nt1 ranges) term)
                  (fun ((l,r), _) -> 
                      (char_of_int (int_of_string (list_to_string ('0' :: 'x' :: r))))) str

and nt_string_meta_char str =
  let slash = pack (word "\\\\") (fun _ -> char_of_int 92) in
  let double_quote = pack (word "\\\"") (fun _ -> char_of_int 34) in
  let tab = pack (word_ci "\\t") (fun _ -> char_of_int 9) in
  let page = pack (word_ci "\\f") (fun _ -> char_of_int 12) in
  let newline = pack (word_ci "\\n") (fun _ -> char_of_int 10) in
  let ret = pack (word_ci "\\r") (fun _ -> char_of_int 13) in
  let double_tilda = pack (word "~~") (fun _ -> char_of_int 126) in
  disj_list [slash; double_quote; tab; page; newline; ret; double_tilda] str

and nt_string_interpolated str =
  let nt1 = nt_sexpr in
  let nt1 = caten nt_skip_star nt1 in
  let nt2 = pack nt1 (fun (_, x)-> x) in
  let nt2 = caten nt2 nt_skip_star in
  let nt2 = pack nt2 (fun (s, _)-> s) in
  let nt2 = caten (word "~{") nt2 in
  let nt2 = pack nt2 (fun (_, sexpr)-> ScmPair((ScmSymbol "format"), ScmPair((ScmString "~a"), ScmPair(sexpr, ScmNil)))) in
  let nt3 = caten nt2 (char '}') in
  let nt3 = pack nt3 (fun (sexpr, _)-> sexpr) in
  nt3 str

(*Came with the code:*)
and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str

 and nt_list str =
 let nt1 = caten nt_skip_star (char ')') in
 let nt1 = caten (caten (char '(') (star (nt_sexpr))) nt1 in
 let nt1 = pack nt1 
            (fun ((_, s), (_, _)) ->
                List.fold_right (fun x y -> ScmPair(x, y)) s ScmNil) in
 nt1 str 

and nt_improper_list str =
 let nt1 = caten (caten (caten (caten (char '(') (plus nt_sexpr)) (char '.')) nt_sexpr) (char ')') in
 let nt2 = pack nt1 
            (fun (((((_, sexps), _), sexp), _)) ->
                  List.fold_right (fun x y -> ScmPair(x, y)) sexps sexp) in
 nt2 str

and nt_quote str = 
  pack (caten (word "\'") nt_sexpr)
      (fun (_, x) ->
            ScmPair(ScmSymbol("quote"), ScmPair(x, ScmNil)))
  str

and nt_quasi_quoted str = 
  pack (caten (word "`") nt_sexpr)
      (fun (_, x) ->
            ScmPair(ScmSymbol("quasiquote"), ScmPair(x, ScmNil)))
  str

and nt_unquoted str = 
  pack (caten (word ",") nt_sexpr)
      (fun (_, x) ->
            ScmPair(ScmSymbol("unquote"), ScmPair(x, ScmNil)))
  str

and nt_unqoute_and_spliced str = 
  pack (caten (word ",@") nt_sexpr)
      (fun (_, x) ->
            ScmPair(ScmSymbol("unquote-splicing"), ScmPair(x, ScmNil)))
  str

and nt_sexpr str =
  let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
               nt_string; nt_vector; nt_list; nt_improper_list; nt_quote; nt_quasi_quoted; nt_unquoted; nt_unqoute_and_spliced] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;

end;; 
(* end of struct Reader *)

let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;
