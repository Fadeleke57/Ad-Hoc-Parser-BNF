(* BEGIN UTILITY FUNCTIONS *)

let is_lower_case c =
  'a' <= c && c <= 'z'

let is_upper_case c =
  'A' <= c && c <= 'Z'

let is_alpha c =
  is_lower_case c || is_upper_case c

let is_digit c =
  '0' <= c && c <= '9'

let is_alphanum c =
  is_lower_case c ||
  is_upper_case c ||
  is_digit c

let is_blank c =
  String.contains " \012\n\r\t" c

let explode s =
  List.of_seq (String.to_seq s)

let implode ls =
  String.of_seq (List.to_seq ls)

(* `span p l = (ft, bk)` where `ft` is the longest prefix of `l` such
   that `p x` is true for every element of `ft` and `ft @ bk = l`.
*)
let span (p : 'a -> bool) (l : 'a list) : 'a list * 'a list =
  let rec go acc r =
    match r with
    | [] -> l, []
    | x :: xs ->
      if p x
      then go (x :: acc) xs
      else List.rev acc, r
  in go [] l


(* END UTILITY FUNCTIONS *)

(* ============================================================ *)

(* Tokenizing*)

type token
  =
  | EqT             (* ::= *)
  | NtmT of string  (* <id> *)
  | TmT of string   (* id *)
  | PdT             (* . *)
  | EOFT            (* end of file *)

let next_token (cs : char list) : (token * char list) option =

  let remove_leading_whitespace cs =  (*returns a char list without the leading whitespace*)
    let result = span (is_blank) (cs) in 
    match result with
    | _, xs -> xs
  in
  let is_equals_symbol cs = (*checks if we can form the ::= symbol with the first 3 characters and returns true or false*)
    match cs with
    | [] -> None
    | x :: y :: z :: rest -> (if x = ':' && y = ':' && z = '=' then Some (EqT, rest) else None)
    | _ -> None
  in
  let rec try_terminal_symbol cs acc = (*trys to find a valid terminal symbol ending with a whitespace*)
    match cs with 
    | x :: xs -> (if is_lower_case x then try_terminal_symbol xs (acc @ [x]) else if is_blank x || x = '<' || x = '.' then Some (TmT (implode acc), [x] @ xs) else None)
    | _ -> None
  in
  let rec try_non_terminal_symbol cs = (*trys to find a valid non-terminal symbol ending with a whitespace*)
    let rest = 
    match cs with
    | [] -> []
    | x :: xs -> xs
    in
    let rec go cs acc =
      match cs with 
      | [] -> None
      | x :: xs -> (if is_lower_case x then go xs (acc @ [x]) else if (x = '>') then Some (NtmT (implode acc), xs) else None)
    in
    go rest []
  in
  let is_period cs = (*returns proper token with rest of list*)
    match cs with
    | x :: xs -> (if x = '.' then Some (PdT, xs) else None)
    | [] -> None
  in
  let classify (cs : char list) : (token * char list) option  = (*main*)
    let first_char = 
      match cs with
      | x :: xs -> [x]
      | [] -> []
    in
    match first_char with
    | [] -> Some (EOFT, [])
    | x -> if x = ['.'] then is_period cs else if x = ['<'] then try_non_terminal_symbol cs else if x = [':'] then is_equals_symbol cs else try_terminal_symbol cs []
    
  in classify (remove_leading_whitespace cs)

let tokenize (s : string) : (token list) option =
  let rec go cs =
    match next_token cs with
    | None -> None
    | Some (EOFT, _) -> Some []
    | Some (t, []) -> Some [t]
    | Some (t, rest) ->
      match go rest with
      | None -> None
      | Some ts -> Some (t :: ts)
  in go (explode s)


let _ = assert(next_token (explode "\n ::= q[qpo;laksjd") = Some (EqT, explode " q[qpo;laksjd"))
let _ = assert(next_token (explode "<asdf>   ...") = Some (NtmT "asdf", explode "   ..."))
let _ = assert(next_token (explode "   term  term ") = Some (TmT "term", explode "  term "))
let _ = assert(next_token (explode "...") = Some (PdT, explode ".."))
let _ = assert(next_token (explode " \n \t \r   ") = Some (EOFT, []))
let _ = assert(next_token (explode "<not-good>") = None)

let _ = assert(tokenize "..::=" = Some [PdT;PdT;EqT])
let _ = assert(tokenize "<a> ::= aab a<b>a." = Some [NtmT "a"; EqT; TmT "aab"; TmT "a"; NtmT "b"; TmT "a"; PdT])
let _ = assert(tokenize "<a> ::= aab a<no-good>a." = None)

(* ============================================================ *)

(* ADTs *)

type symbol
  = NT of string
  | T of string

type sentform = symbol list
type rule = string * sentform
type grammar = rule list

let expand_leftmost ((nt, sf) : rule) (s : sentform) : sentform =
  let expand (nonT : string) = (*if id matches the non-terminal, then expand the non-terminal to match the rule*)
    match nt = nonT with
    | false -> [NT nonT]
    | true -> sf
  in

  let rec helper (r : rule) (s : sentform) (acc : sentform) : sentform = (*main*)
    match s with
    | [] -> acc
    | T x :: rest ->  helper r rest (acc @ [T x]) (*if just T ignore it but add it to the final expanded list*)
    | NT x :: rest -> if x = nt then acc @ (expand x) @ rest else helper r rest (acc @ (expand x)) (*if leftmost NT is reached end otherwise check the rest of the list *)
  in helper ((nt, sf)) (s) []

(*da rulez*)
(* <a> ::= a<a>. *) 
let r = "b", [T "b"; NT "a";T "b"]

(* <a> --> a<a> *)
let _ = assert (expand_leftmost r [NT "b"] = [T "b"; NT "a";T "b"])
(* <a> --> a<a> --> aa<a> *)
let _ = assert (expand_leftmost r (expand_leftmost r [NT "b"]) = [T "b"; NT "a";T "b"])
(* <a>b<a> --> a<a>b<a> *)
let _ = assert (expand_leftmost r [NT "b"; T "d"; NT "a"; NT "b"] = [T "b"; NT "a"; T "b"; T "d"; NT "a"; NT "b"])

(* ============================================================ *)

(* Parsing BNF Specifications*)

let rec parse_sentform (ts : token list) : (sentform * token list) option =
  let rec extract_valid_tokens tokens acc = (*returns the first k valid tokens and the rest of the list*)
    match tokens with
    | [] -> None
    | NtmT x :: rest -> extract_valid_tokens rest (acc @ [NT x])  
    | TmT x :: rest -> extract_valid_tokens rest (acc @ [T x]) 
    | x :: rest -> Some (acc, ([x] @ rest))
  in
  let first_token = (*first token of the token list*)
    match ts with
    | [] -> None
    | x :: xs -> Some x
  in
  let parse tokens = (*main*)
    match first_token with
    | Some NtmT x -> extract_valid_tokens tokens []
    | Some TmT x -> extract_valid_tokens tokens []
    | _ -> None
  in
  parse ts

let parse_rule (ts : token list) : (rule * token list) option =
  let rec extract_valid_rule (tokens : token list) (acc : sentform) (rule : string) = (*please work*) (*should already check for missing periods*)
    match tokens with
    | [] -> None
    | PdT :: rest -> Some ((rule, acc), rest)              
    | NtmT x :: rest -> extract_valid_rule (rest) (acc @ [NT x]) rule
    | TmT x :: rest -> extract_valid_rule (rest) (acc @ [T x]) rule
    | x -> None
  in
  let is_rule_start = (*checks if this is this a valid rule*)
    match ts with 
    | [] -> false
    | NtmT x :: EqT :: TmT y :: rest -> true
    | NtmT x :: EqT :: NtmT y :: rest -> true
    | _ -> false
  in
  let parse tokens = (*if the start of the tokens is a valid rule, extract the rule*)
    match is_rule_start with
    | false -> None
    | true -> (
      match tokens with
      | NtmT x :: y :: rest -> extract_valid_rule rest [] x
      | _ -> None
    )
  in
  parse ts

let rec parse_grammar (ts : token list) : grammar * token list = 
  let rec add_rules tokens acc = (**)
    let first_rule = parse_rule tokens in
    match first_rule with
    | None -> acc, tokens
    | Some (x, rest) -> add_rules rest (x :: acc)
  in
  let (g, rest) = add_rules ts [] in
  (List.rev g, rest)
let is_empty lst = (*List.is_empty isn't supported for me for some reason so i made my own is_empty func*)
  match lst with
  | [] -> true
  | _ -> false

let parse_and_check (s : string) : grammar option =
  match tokenize s with
  | None -> None
  | Some ts ->
    let (g, rest) = parse_grammar ts in
    if is_empty rest (*List.is_empty isn't supported for me for some reason so i made my own is_empty func*)
    then Some g
    else None


let _ = assert (parse_sentform [NtmT "a"; TmT "b"; NtmT "a"; PdT; PdT; PdT] = Some ([NT "a"; T "b"; NT "a"], [PdT; PdT; PdT]))
let _ = assert (parse_sentform [PdT; PdT; PdT] = None)

let _ = assert (parse_rule [NtmT "a"; EqT; TmT "a"; NtmT "a"; PdT; PdT; PdT] = Some (("a", [T "a"; NT "a"]), [PdT; PdT]))
let _ = assert (parse_rule [NtmT "a"; EqT; TmT "a"; NtmT "a"; NtmT "a"; EqT; NtmT "a"] = None)


let simple_test = "
  <a> ::= a <a> a b .
  <a> ::= <b> .
  <b> ::= b <b> .
  <b> ::= <c> .
  <c> ::= b .
  <c> ::= e f .
  <c> ::= g .
"

let simple_test_out =
  [ "a", [T "a"; NT "a"; T "a"; T "b"]
  ; "a", [NT "b"]
  ; "b", [T "b"; NT "b"]
  ; "b", [NT "c"]
  ; "c", [T "b"]
  ; "c", [T "e"; T "f"]
  ; "c", [T "g"]
  ]

let simple_test_missing_period = "
  <a> ::= a <a> a b .
  <a> ::= <b>
  <b> ::= b <b> .
  <b> ::= <c> .
  <c> ::= d .
  <c> ::= e f .
  <c> ::= g .
"


let _ = assert (parse_and_check simple_test = Some simple_test_out)
let _ = assert (parse_and_check simple_test_missing_period = None)
