open Z3
open Z3.Solver
open Z3.Arithmetic

module Solver = struct
  let ctx = mk_context []
  
  let rec mk_expr (e : Loop.aexpr) =
    match e with
    | Var n -> Integer.mk_const ctx (Symbol.mk_string ctx (Opal.implode n))
    | Cst c -> Integer.mk_numeral_i ctx (Parser.Compat.z_to_int c)
    | Add (e1, e2) -> mk_add ctx [mk_expr e1; mk_expr e2]
    | Sub (e1, e2) -> mk_sub ctx [mk_expr e1; mk_expr e2]

  let rec mk_form (e : Loop.bexpr) =
    match e with
    | Bcst true -> Boolean.mk_true ctx
    | Bcst false -> Boolean.mk_false ctx
    | Band (l, r) -> Boolean.mk_and ctx [mk_form l; mk_form r]
    | Ble (e1, e2) -> mk_le ctx (mk_expr e1) (mk_expr e2)
    | Beq (e1, e2) -> Boolean.mk_eq ctx (mk_expr e1) (mk_expr e2)
    | Bnot f -> Boolean.mk_not ctx (mk_form f)

  let sat (f : Loop.bexpr) =
    let slv = mk_simple_solver ctx in
    let pro = mk_form f in
    add slv [pro];
    match check slv [] with
    | SATISFIABLE -> Some true
    | UNSATISFIABLE -> Some false
    | UNKNOWN -> None
end