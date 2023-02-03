
type nat =
| O
| S of nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val eqb : bool -> bool -> bool

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val eqb : z -> z -> bool
 end

val eqb0 : char list -> char list -> bool

type 'a stream = 'a __stream Lazy.t
and 'a __stream =
| Scons of 'a * 'a stream

val peek : nat -> 'a1 stream -> 'a1 list

val map0 : ('a1 -> 'a2) -> 'a1 stream -> 'a2 stream

type ident = char list

type aexpr =
| Var of ident
| Cst of z
| Add of aexpr * aexpr
| Sub of aexpr * aexpr

val aeq : aexpr -> aexpr -> bool

type bexpr =
| Bcst of bool
| Ble of aexpr * aexpr
| Beq of aexpr * aexpr
| Bnot of bexpr
| Band of bexpr * bexpr

val beq : bexpr -> bexpr -> bool

type iMP =
| Skip
| Ite of bexpr * iMP * iMP
| Seq of iMP * iMP
| Aff of char list * aexpr
| Err
| Loop of bexpr * iMP

val is_error : iMP -> bool

type sym_store = ident -> aexpr

val id : sym_store

val sym_update : sym_store -> ident -> aexpr -> sym_store

val sym_aeval : sym_store -> aexpr -> aexpr

val sym_beval : sym_store -> bexpr -> bexpr

type sym_state = (bexpr * sym_store) * iMP

type tasks = sym_state list

type status =
| BugFound of sym_state
| Pending
| Finished

val then_do : iMP -> sym_state -> (bexpr * sym_store) * iMP

val expand : bexpr -> sym_store -> iMP -> sym_state list

val run : tasks -> sym_state option stream

val display : sym_state option -> status

val init : iMP -> sym_state list

val find_bugs : iMP -> status stream

val init_assuming : iMP -> bexpr -> ((bexpr * sym_store) * iMP) list

val find_bugs_assuming : iMP -> bexpr -> status stream

val mk_add : aexpr -> aexpr -> aexpr

val mk_sub : aexpr -> aexpr -> aexpr

val asimp : aexpr -> aexpr

val mk_and : bexpr -> bexpr -> bexpr

val mk_not : bexpr -> bexpr

val bsimp : bexpr -> bexpr
