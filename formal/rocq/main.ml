(* emdref-rocq: runs the extracted Rocq model. Same interface and output as the
   Lean emdref, so crates/emd-vm/tests/differential.rs can compare all three. *)

open Emd_extracted

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

(* Strict UTF-8, as the Rust parser and the Lean interpreter read it: an overlong or
   otherwise invalid sequence must not turn into a dash. None if the bytes are invalid. *)
let code_points s =
  let n = String.length s in
  let rec go i acc =
    if i >= n then Some (List.rev acc)
    else
      let d = String.get_utf_8_uchar s i in
      if Uchar.utf_decode_is_valid d then
        go (i + Uchar.utf_decode_length d) (Uchar.to_int (Uchar.utf_decode_uchar d) :: acc)
      else None
  in
  go 0 []

let rec pos_to_int64 = function
  | XH -> 1L
  | XO p -> Int64.mul 2L (pos_to_int64 p)
  | XI p -> Int64.add (Int64.mul 2L (pos_to_int64 p)) 1L

let z_to_string = function
  | Z0 -> "0"
  | Zpos p -> Int64.to_string (pos_to_int64 p)
  | Zneg p -> "-" ^ Int64.to_string (pos_to_int64 p)

let show strings = "[" ^ String.concat ", " strings ^ "]"

let print_state s =
  print_string
    ("stack " ^ show (List.map z_to_string s.stack) ^ "\n");
  print_string
    ("output " ^ show (List.map string_of_int s.output) ^ "\n")

let fault_name = function
  | StackUnderflow -> "stackUnderflow"
  | DivisionByZero -> "divisionByZero"
  | NegativeAddress -> "negativeAddress"
  | PcOutOfRange -> "pcOutOfRange"
  | InvalidByte -> "invalidByte"

let () =
  let source = read_file Sys.argv.(1) in
  let input = read_file Sys.argv.(2) in
  let fuel = int_of_string Sys.argv.(3) in
  let program =
    match Option.bind (code_points source) decode_source with
    | Some p -> p
    | None -> prerr_endline "undecodable"; exit 1
  in
  let bytes = List.map Char.code (List.of_seq (String.to_seq input)) in
  match run program fuel (init bytes) with
  | Halted s -> print_string "halt\n"; print_state s
  | Next s -> print_string "running\n"; print_state s
  | Faulted f -> print_string ("fault Emd.Fault." ^ fault_name f ^ "\n")
