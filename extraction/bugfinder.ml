open Loop
open Solver

(* let prog = Ite (Bcst True, Err, Skip) *)

let rec print_bexpr fmt (b : bexpr) =
  match b with
  | Bcst true -> Printf.fprintf fmt "true"
  | Bcst false -> Printf.fprintf fmt "false"
  | Ble (x, y) -> Printf.fprintf fmt "(%a <= %a)" print_aexpr x print_aexpr y
  | Beq (x, y) -> Printf.fprintf fmt "(%a = %a)" print_aexpr x print_aexpr y
  | Bnot x -> Printf.fprintf fmt "(not %a)" print_bexpr x
  | Band (x, y) -> Printf.fprintf fmt "(%a and %a)" print_bexpr x print_bexpr y

and print_aexpr fmt a =
  match a with
  | Var x -> Printf.fprintf fmt "%s" (Opal.implode x)
  | Cst z -> Printf.fprintf fmt "%d" (Parser.Compat.z_to_int z)
  | Add (a1, a2) -> Printf.fprintf fmt "(%a + %a)" print_aexpr a1 print_aexpr a2
  | Sub (a1, a2) -> Printf.fprintf fmt "(%a - %a)" print_aexpr a1 print_aexpr a2

let prompt () =
  Printf.printf "Do you want to continue [y/N]\n";
  if read_line () = "y" then ()
  else begin
    Printf.printf "Ending the session\n";
    exit 1
  end

let report (s : status) =
  match s with
  | Pending ->
    print_endline "[\027[93mo\027[0m] => Pending"
  | BugFound ((path, _), _) ->
    begin match Solver.sat path with
    | Some false ->
      Printf.printf "[\027[92mV\027[0m] => Potential bug (CLEARED) %a\n" print_bexpr path
    | Some true ->
      Printf.printf "[\027[31mx\027[0m] => Found bug %a\n" print_bexpr (bsimp path);
      prompt ()
    | None ->
      Printf.printf "[\027[31m?\027[0m] => Potential bug (NOT CLEARED) %a\n" print_bexpr path;
      prompt ()
    end
  | Finished ->
    Printf.printf "Done\n";
    exit 0

let rec iter (str : status stream) (f : status -> unit) : unit =
  match Lazy.force str with
  | Scons (x, xs) ->
    report x; iter xs f

let usage_msg = Sys.argv.(0) ^ " <file1.imp>"
let input_file = ref ""

let anon_fun (_ : String.t) = ()
let speclist = [
  ("-i", Arg.Set_string input_file, "input file")
]

let () =
  Arg.parse speclist anon_fun usage_msg;
  if !input_file = "" then begin
    Printf.eprintf "usage:\n\t%s" usage_msg; exit 1
  end else begin
    let (precond, prog) = Parser.parse_file !input_file in
    iter (find_bugs_assuming prog precond) report
  end
