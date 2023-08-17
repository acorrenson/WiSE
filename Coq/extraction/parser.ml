open Loop
open Opal

module Compat = struct

let rec nat2int = function
  | O -> 0
  | S n -> 1 + nat2int n

let rec pos_to_int = function
  | XH -> 1
  | XO p -> 2 * (pos_to_int p)
  | XI p -> 1 + 2 * (pos_to_int p)

let z_to_int = function
  | Z0 -> 0
  | Zpos p -> pos_to_int p
  | Zneg p -> -pos_to_int p

let pos_to_z p =
  assert (p > 0);
  let z = ref XH in
  let r = ref (p - 1) in
  while !r > 0 do
    r := !r / 2;
    if !r mod 2 = 0 then
      z := XO !z
    else
      z := XI !z
  done;
  !z

let int_to_nat (i : int) =
  assert (i >= 0);
  let r = ref i in
  let n = ref O in
  while !r > 0 do
    decr r;
    n := S !n
  done;
  !n

let int_to_z (i : int) =
  if i = 0 then
    Z0
  else if i < 0 then
    Zneg (pos_to_z (-i))
  else
    Zpos (pos_to_z i)

(* let char_to_ascii c =
  let cd = Char.code c in
  let b1 = (1 land cd) > 0 in
  let b2 = (2 land cd) > 0 in
  let b3 = (4 land cd) > 0 in
  let b4 = (8 land cd) > 0 in
  let b5 = (16 land cd) > 0 in
  let b6 = (32 land cd) > 0 in
  let b7 = (64 land cd) > 0 in
  let b8 = (128 land cd) > 0 in
  Ascii (
    of_bool b1,
    of_bool b2,
    of_bool b3,
    of_bool b4,
    of_bool b5,
    of_bool b6,
    of_bool b7,
    of_bool b8
  ) *)

(* let ascii_to_char (Ascii (b1, b2, b3, b4, b5, b6, b7, b8)) =
  Char.chr (
    (to_bit b1 lsr 0) lor
    (to_bit b2 lsr 1) lor
    (to_bit b3 lsr 2) lor
    (to_bit b4 lsr 3) lor
    (to_bit b5 lsr 4) lor
    (to_bit b6 lsr 5) lor
    (to_bit b7 lsr 6) lor
    (to_bit b8 lsr 7)
  )

let () =
  Printf.printf "-> %c <-\n" (ascii_to_char (char_to_ascii 'a')) *)

end

let (let*) = (>>=)

let count = ref 0
let fresh () = incr count; !count
let ctx : (string, int) Hashtbl.t = Hashtbl.create 10
let mk_var s =
  match Hashtbl.find_opt ctx s with
  | None ->
    let x = fresh () in
    Hashtbl.add ctx s x;
    x
  | Some x -> x

let parens x = between (exactly '(') (exactly ')') x
let integer = many1 digit => implode % int_of_string % Compat.int_to_z % (fun x -> Cst x)
let ident = (letter <~> many alpha_num) => implode

let add = token "+" >> spaces >> return (fun x y -> Add (x, y))
let sub = token "-" >> spaces >> return (fun x y -> Sub (x, y))
let mul = token "*" >> spaces >> return (fun _ -> assert false)
let div = token "/" >> spaces >> return (fun _ -> assert false)

let rec parse_expr input = chainl1 parse_term (add <|> sub) input
and parse_term input = chainl1 parse_factor (mul <|> div) input
and parse_factor input = (parens parse_expr <|> integer <|> (ident => (fun x -> Var (explode x)))) input

let parse_comp =
  choice [
    token "<=" >> return (fun x y -> Ble (x, y));
    token "<" >> return (fun x y -> Bnot (Ble (y, x)));
    token ">="  >> return (fun x y -> Ble (y, x));
    token ">"  >> return (fun x y -> Bnot (Ble (x, y)));
    token "="  >> return (fun x y -> Beq (x, y));
    token "!=" >> return (fun x y -> Bnot (Beq (x, y)));
  ]

let parse_cond =
  let* l = spaces >> parse_expr in
  let* f = spaces >> parse_comp in
  let* r = spaces >> parse_expr in
  return (f l r)

let band = token "and" >> spaces >> return (fun x y -> Band (x, y))
let bor = token "or" >> spaces >> return (fun x y -> Bnot (Band (Bnot x, Bnot y)))

let rec parse_bexpr input = chainl1 parse_bterm bor input
and parse_bterm input = chainl1 parse_bfactor band input
and parse_bfactor input = (parens parse_bexpr <|> parse_cond) input

let to_seq = function
  | [] -> Skip
  | [x] -> x
  | x::xs -> List.fold_left (fun x y -> Seq (x, y)) x xs

let big_and = function
  | [] -> Bcst true
  | [x] -> x
  | x::xs -> List.fold_left (fun x y -> Band (x, y)) x xs

let parse_asssume =
  token "assume" >> spaces >> parse_bexpr

let parse_assert =
  token "assert" >> spaces >> parse_bexpr => (fun x -> Ite (x, Skip, Err))

let parse_prelude =
  many parse_asssume => big_and

let rec parse_prog input =
  (spaces >> (many parse_stmt => to_seq)) input
and parse_stmt input =
  (spaces >> (parse_if <|> parse_loop <|> parse_aff <|> parse_fail <|> parse_assert)) input
and parse_if input =
  begin
    let* _ = token "if" in
    let* c = spaces >> parse_bexpr in
    let* a = spaces >> between (token "{" << spaces) (token "}" << spaces) parse_prog in
    let* _ = token "else" in
    let* b = spaces >> between (token "{" << spaces) (token "}" << spaces) parse_prog in
    return (Ite (c, a, b))
  end input
and parse_loop input =
  begin
    let* _ = token "loop" in
    let* c = spaces >> parse_bexpr in
    let* b = spaces >> between (token "{" << spaces) (token "}" << spaces) parse_prog in
    return (Loop (c, b))
  end input
and parse_aff input =
  begin
    let* x = (spaces >> ident) in
    let* _ = token "=" in
    let* e = spaces >> parse_expr in
    return (Aff (explode x, e))
  end input
and parse_fail input =
  (token "fail" >> return Err) input

let parse_unit =
  let* prelude = parse_prelude in
  let* body = parse_prog in
  return (prelude, body)

let parse_file f =
  let inx = open_in f in
  let stream = LazyStream.of_channel inx in
  match (parse_unit << spaces) stream with
  | Some (x, Nil) -> x
  | _ -> failwith "parse error"