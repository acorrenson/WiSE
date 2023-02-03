
type nat =
| O
| S of nat

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> false)
 end

(** val eqb0 : char list -> char list -> bool **)

let rec eqb0 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb0 s1' s2' else false)

type 'a stream = 'a __stream Lazy.t
and 'a __stream =
| Scons of 'a * 'a stream

(** val peek : nat -> 'a1 stream -> 'a1 list **)

let rec peek n s =
  match n with
  | O -> []
  | S n0 -> let Scons (x, xs) = Lazy.force s in x :: (peek n0 xs)

(** val map0 : ('a1 -> 'a2) -> 'a1 stream -> 'a2 stream **)

let rec map0 f s =
  let Scons (x, xs) = Lazy.force s in lazy (Scons ((f x), (map0 f xs)))

type ident = char list

type aexpr =
| Var of ident
| Cst of z
| Add of aexpr * aexpr
| Sub of aexpr * aexpr

(** val aeq : aexpr -> aexpr -> bool **)

let rec aeq a1 a2 =
  match a1 with
  | Var id1 -> (match a2 with
                | Var id2 -> eqb0 id1 id2
                | _ -> false)
  | Cst c1 -> (match a2 with
               | Cst c2 -> Z.eqb c1 c2
               | _ -> false)
  | Add (a3, a4) ->
    (match a2 with
     | Add (a5, a6) -> (&&) (aeq a3 a5) (aeq a4 a6)
     | _ -> false)
  | Sub (a3, a4) ->
    (match a2 with
     | Sub (a5, a6) -> (&&) (aeq a3 a5) (aeq a4 a6)
     | _ -> false)

type bexpr =
| Bcst of bool
| Ble of aexpr * aexpr
| Beq of aexpr * aexpr
| Bnot of bexpr
| Band of bexpr * bexpr

(** val beq : bexpr -> bexpr -> bool **)

let rec beq b1 b2 =
  match b1 with
  | Bcst b3 -> (match b2 with
                | Bcst b4 -> eqb b3 b4
                | _ -> false)
  | Ble (a1, a2) ->
    (match b2 with
     | Ble (a3, a4) -> (&&) (aeq a1 a3) (aeq a2 a4)
     | _ -> false)
  | Beq (a1, a2) ->
    (match b2 with
     | Beq (a3, a4) -> (&&) (aeq a1 a3) (aeq a2 a4)
     | _ -> false)
  | Bnot b3 -> (match b2 with
                | Bnot b4 -> beq b3 b4
                | _ -> false)
  | Band (b3, b4) ->
    (match b2 with
     | Band (b5, b6) -> (&&) (beq b3 b5) (beq b4 b6)
     | _ -> false)

type iMP =
| Skip
| Ite of bexpr * iMP * iMP
| Seq of iMP * iMP
| Aff of char list * aexpr
| Err
| Loop of bexpr * iMP

(** val is_error : iMP -> bool **)

let rec is_error = function
| Seq (p0, _) -> is_error p0
| Err -> true
| _ -> false

type sym_store = ident -> aexpr

(** val id : sym_store **)

let id x =
  Var x

(** val sym_update : sym_store -> ident -> aexpr -> sym_store **)

let sym_update s x e y =
  if eqb0 y x then e else s y

(** val sym_aeval : sym_store -> aexpr -> aexpr **)

let rec sym_aeval s e = match e with
| Var x -> s x
| Cst _ -> e
| Add (e1, e2) -> Add ((sym_aeval s e1), (sym_aeval s e2))
| Sub (e1, e2) -> Sub ((sym_aeval s e1), (sym_aeval s e2))

(** val sym_beval : sym_store -> bexpr -> bexpr **)

let rec sym_beval s e = match e with
| Bcst _ -> e
| Ble (e1, e2) -> Ble ((sym_aeval s e1), (sym_aeval s e2))
| Beq (e1, e2) -> Beq ((sym_aeval s e1), (sym_aeval s e2))
| Bnot e0 -> Bnot (sym_beval s e0)
| Band (e1, e2) -> Band ((sym_beval s e1), (sym_beval s e2))

type sym_state = (bexpr * sym_store) * iMP

type tasks = sym_state list

type status =
| BugFound of sym_state
| Pending
| Finished

(** val then_do : iMP -> sym_state -> (bexpr * sym_store) * iMP **)

let then_do q = function
| (p0, p) -> (p0, (Seq (p, q)))

(** val expand : bexpr -> sym_store -> iMP -> sym_state list **)

let rec expand path env = function
| Ite (b, p1, p2) ->
  (((Band (path, (sym_beval env b))), env), p1) :: ((((Band (path, (Bnot
    (sym_beval env b)))), env), p2) :: [])
| Seq (p1, p2) ->
  (match p1 with
   | Skip -> ((path, env), p2) :: []
   | _ -> map (then_do p2) (expand path env p1))
| Aff (x, e) -> ((path, (sym_update env x (sym_aeval env e))), Skip) :: []
| Loop (b, p) ->
  (((Band (path, (sym_beval env b))), env), (Seq (p, (Loop (b,
    p))))) :: ((((Band (path, (Bnot (sym_beval env b)))), env), Skip) :: [])
| _ -> []

(** val run : tasks -> sym_state option stream **)

let rec run = function
| [] -> lazy (Scons (None, (run [])))
| s :: next ->
  let (p, prog) = s in
  let (path, env) = p in
  let next_next = expand path env prog in
  lazy (Scons ((Some ((path, env), prog)), (run (app next next_next))))

(** val display : sym_state option -> status **)

let display = function
| Some s ->
  let (p, prog) = s in if is_error prog then BugFound (p, prog) else Pending
| None -> Finished

(** val init : iMP -> sym_state list **)

let init p =
  (((Bcst true), id), p) :: []

(** val find_bugs : iMP -> status stream **)

let find_bugs p =
  map0 display (run (init p))

(** val init_assuming : iMP -> bexpr -> ((bexpr * sym_store) * iMP) list **)

let init_assuming p cond =
  ((cond, id), p) :: []

(** val find_bugs_assuming : iMP -> bexpr -> status stream **)

let find_bugs_assuming p cond =
  map0 display (run (init_assuming p cond))

(** val mk_add : aexpr -> aexpr -> aexpr **)

let mk_add a1 a2 =
  match a1 with
  | Cst c1 ->
    (match a2 with
     | Cst c2 -> Cst (Z.add c1 c2)
     | Sub (a2_1, a2_2) -> if aeq a1 a2_2 then a2_1 else Add (a1, a2)
     | _ -> Add (a1, a2))
  | _ ->
    (match a2 with
     | Sub (a2_1, a2_2) -> if aeq a1 a2_2 then a2_1 else Add (a1, a2)
     | _ -> Add (a1, a2))

(** val mk_sub : aexpr -> aexpr -> aexpr **)

let mk_sub a1 a2 =
  match a1 with
  | Cst c1 ->
    (match a2 with
     | Cst c2 -> Cst (Z.sub c1 c2)
     | Add (a2_1, a2_2) ->
       if aeq a1 a2_1
       then Sub ((Cst Z0), a2_2)
       else if aeq a1 a2_2 then Sub ((Cst Z0), a2_1) else Sub (a1, a2)
     | _ -> Sub (a1, a2))
  | _ ->
    (match a2 with
     | Add (a2_1, a2_2) ->
       if aeq a1 a2_1
       then Sub ((Cst Z0), a2_2)
       else if aeq a1 a2_2 then Sub ((Cst Z0), a2_1) else Sub (a1, a2)
     | _ -> Sub (a1, a2))

(** val asimp : aexpr -> aexpr **)

let rec asimp a = match a with
| Add (a0, b) -> mk_add (asimp a0) (asimp b)
| Sub (a0, b) -> mk_sub (asimp a0) (asimp b)
| _ -> a

(** val mk_and : bexpr -> bexpr -> bexpr **)

let mk_and b1 b2 =
  match b1 with
  | Bcst b ->
    if b
    then (match b2 with
          | Bcst b0 -> if b0 then b2 else Bcst false
          | _ -> b2)
    else Bcst false
  | Bnot lhs ->
    (match b2 with
     | Bcst b -> if b then b1 else Bcst false
     | Bnot rhs -> if beq b1 rhs then Bcst false else Band (b1, (Bnot rhs))
     | _ -> if beq lhs b2 then Bcst false else Band ((Bnot lhs), b2))
  | Band (_, _) ->
    (match b2 with
     | Bcst b3 -> if b3 then b1 else Bcst false
     | Bnot rhs -> if beq b1 rhs then Bcst false else Band (b1, (Bnot rhs))
     | _ -> if beq b1 b2 then b1 else Band (b1, b2))
  | _ ->
    (match b2 with
     | Bcst b -> if b then b1 else Bcst false
     | Bnot rhs -> if beq b1 rhs then Bcst false else Band (b1, (Bnot rhs))
     | _ -> if beq b1 b2 then b1 else Band (b1, b2))

(** val mk_not : bexpr -> bexpr **)

let mk_not b = match b with
| Bcst b0 -> if b0 then Bcst false else Bcst true
| Bnot lhs -> lhs
| _ -> Bnot b

(** val bsimp : bexpr -> bexpr **)

let rec bsimp b = match b with
| Bcst _ -> b
| Ble (x, y) ->
  (match asimp x with
   | Cst x0 ->
     let x1 = Cst x0 in
     (match asimp y with
      | Cst y0 -> Bcst (Z.leb x0 y0)
      | x2 -> Ble (x1, x2))
   | x0 -> Ble (x0, (asimp y)))
| Beq (x, y) ->
  (match asimp x with
   | Cst x0 ->
     let x1 = Cst x0 in
     (match asimp y with
      | Cst y0 -> Bcst (Z.eqb x0 y0)
      | x2 -> if aeq x1 x2 then Bcst true else Beq (x1, x2))
   | x0 -> if aeq x0 (asimp y) then Bcst true else Beq (x0, (asimp y)))
| Bnot lhs -> mk_not (bsimp lhs)
| Band (lhs, rhs) -> mk_and (bsimp lhs) (bsimp rhs)
