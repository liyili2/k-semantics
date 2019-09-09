
let _ =
  if "20120619" <> Dyp.version
  then (Printf.fprintf stderr
    "version mismatch, dypgen version 20120619 and dyplib version %s\n" Dyp.version;
  exit 2)

module Dyp_symbols =
struct
  let get_token_name () = 0
  let str_token _ = failwith "str_token must not be called with dypgen lexers"
  let ter_string_list = [
      ("__dypgen_layout",0);]
end

type ('dypgen__Obj_expr, 'dypgen__Obj_main) obj =
  | Lexeme_matched of string
  | Obj___dypgen_layout
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of 'dypgen__Obj_main
  | Dypgen__dummy_obj_cons

module Dyp_symbols_array =
struct
  let token_name_array =
  [|"__dypgen_layout"|]
  let nt_cons_list =
  [
    ("expr",1);
    ("main",2)]
  let str_cons o = match o with
    | Lexeme_matched _ -> "Lexeme_matched"
    | Obj_expr _ -> "Obj_expr"
    | Obj_main _ -> "Obj_main"
    | _ -> failwith "str_cons, unexpected constructor"
  let cons_array = [|
    "Lexeme_matched";
    "Obj_expr";
    "Obj_main";
    "";
  |]
  let entry_points = [
    "main";]
end

let dypgen_lexbuf_position lexbuf = Dyp.dyplex_lexbuf_position lexbuf

module Dyp_aux_functions =
struct
  let get_token_value _ = Dypgen__dummy_obj_cons
  let cons_table = Dyp.Tools.hashtbl_of_array Dyp_symbols_array.cons_array
end

module Dyp_priority_data =
struct
  let relations = [
  ]
end

let global_data = ()
let local_data = ()
let global_data_equal = (==)
let local_data_equal = (==)

let dyp_merge_Lexeme_matched = Dyp.Tools.keep_zero
let dyp_merge_Obj_expr = Dyp.Tools.keep_zero
let dyp_merge_Obj_main = Dyp.Tools.keep_zero
let dyp_merge = Dyp.keep_one
let dypgen_match_length = `shortest
let dypgen_choose_token = `first
let dypgen_keep_data = `both
let dypgen_use_rule_order = false
let dypgen_use_all_actions = false

# 1 "position_parser.dyp"

open Dyp
open Parse_tree
open Lexing

let print_pos pos =
  Printf.printf "fname=%s, lnum=%d, bol=%d, cnum=%d\n"
    pos.pos_fname pos.pos_lnum pos.pos_bol
      pos.pos_cnum;
  flush_all ()

let update_loc lexbuf file line absolute chars =
  let pos = lexbuf.lex_curr_p in
  let new_file = match file with
                 | None -> pos.pos_fname
                 | Some s -> s
  in
  lexbuf.lex_curr_p <- { pos with
    pos_fname = new_file;
    pos_lnum = if absolute then line else pos.pos_lnum + line;
    pos_bol = pos.pos_cnum - chars;
  }

let _ = () (* dummy line to improve OCaml error location *)
# 101                "position_parser_temp.ml"
let __dypgen_ra_list, __dypgen_main_lexer, __dypgen_aux_lexer =
[
(("main",[Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Regexp (Dyp.RE_Eof_char)],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_expr ( (
(_:'dypgen__Obj_expr)
# 108                "position_parser_temp.ml"
 as _1)); Lexeme_matched _2] -> Obj_main 
# 30 "position_parser.dyp"
(
                ( _1 ):'dypgen__Obj_main)
# 113                "position_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Regexp (Dyp.RE_Plus (Dyp.RE_Char_set [('0','9')]))],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ Lexeme_matched _1] -> Obj_expr 
# 33 "position_parser.dyp"
(
               (
      Printf.printf "int:%s\n" _1;
      Printf.printf "%d--%d\n" (dyp.symbol_start ()) (dyp.symbol_end ());
      print_pos (dyp.symbol_start_pos ());
      print_pos (dyp.symbol_end_pos ());
      Int (int_of_string _1) ):'dypgen__Obj_expr)
# 128                "position_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String "+");Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String "*");Dyp.Non_ter ("expr",Dyp.No_priority )],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_expr ( (
(_:'dypgen__Obj_expr)
# 136                "position_parser_temp.ml"
 as _1)); Lexeme_matched _2;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 139                "position_parser_temp.ml"
 as _3)); Lexeme_matched _4;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 142                "position_parser_temp.ml"
 as _5))] -> Obj_expr 
# 39 "position_parser.dyp"
(
                           (
      print_tree (Node (_1,_3,_5));
      print_newline ();
      Printf.printf "%d--%d\n" (dyp.symbol_start ()) (dyp.symbol_end ());
      print_pos (dyp.symbol_start_pos ());
      print_pos (dyp.symbol_end_pos ());
      print_endline "rhs positions";
      let _ = for i=1 to 5 do
        Printf.printf "symb %d\n" i;
        Printf.printf "%d--%d\n" (dyp.rhs_start i) (dyp.rhs_end i);
        print_pos (dyp.Dyp.rhs_start_pos i);
        print_pos (dyp.Dyp.rhs_end_pos i)
      done in
      print_newline ();
      Node (_1,_3,_5) ):'dypgen__Obj_expr)
# 161                "position_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])],

([
  ("__dypgen_layout",(Dyp.RE_Char_set [(' ',' ');('\t','\t')]));
  ("__dypgen_layout",(Dyp.RE_Char '\n'))],
[
  0,((fun lexbuf -> Obj___dypgen_layout));
  0,((fun lexbuf -> let _ = (
# 27 "position_parser.dyp"
              update_loc (Dyp.std_lexbuf lexbuf) None 1 false 0 
# 173                "position_parser_temp.ml"
) in Obj___dypgen_layout))]),

[]

let __dypgen_regexp_decl = []

let dyp_merge_Lexeme_matched l =
  match dyp_merge_Lexeme_matched l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_expr l =
  match dyp_merge_Obj_expr l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_main l =
  match dyp_merge_Obj_main l with
    | ([],_,_) -> dyp_merge l
    | res -> res

let __dypgen_merge_list = [(fun l -> (
  let f1 (o,gd,ld) = match o with Lexeme_matched ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Lexeme_matched"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Lexeme_matched l in
  let f2 o = Lexeme_matched o in
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Obj_expr ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_expr"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_expr l in
  let f2 o = Obj_expr o in
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Obj_main ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_main"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_main l in
  let f2 o = Obj_main o in
  (List.map f2 ol, gd, ld)))]



let __dypgen_test_cons () =  [|
  (fun x -> match x with Lexeme_matched _ -> true | _ -> false);
  (fun x -> match x with Obj_expr _ -> true | _ -> false);
  (fun x -> match x with Obj_main _ -> true | _ -> false)|]

let __dypgen_dummy_marker_2 = ()
let pp () = Dyp.make_parser
  __dypgen_ra_list Dyp_priority_data.relations global_data local_data
  (Dyp.Tools.make_nt_cons_map Dyp_symbols_array.nt_cons_list)
  Dyp_symbols_array.entry_points
  
  true 1 true
  
  Dyp_aux_functions.get_token_value
  Dyp_symbols.get_token_name Dyp_symbols.str_token
  global_data_equal local_data_equal (__dypgen_test_cons ())
  Dyp_symbols_array.str_cons
  Dyp_symbols_array.cons_array Dyp_aux_functions.cons_table
  (Dyp.Tools.array_of_list __dypgen_merge_list)
  dypgen_lexbuf_position __dypgen_regexp_decl __dypgen_main_lexer
  __dypgen_aux_lexer Dyp_symbols.ter_string_list
  (fun lexbuf -> Lexeme_matched (Dyp.lexeme lexbuf))
  true


let __dypgen_dummy_marker_5 = ()

let __dypgen_dummy_marker_3 = ()

let main ?(global_data=global_data) ?(local_data=local_data) lexbuf =
  let pf = Dyp.lexparse (pp ()) "main" ~global_data:global_data
    ~local_data:local_data ~match_len:dypgen_match_length
    ~keep_data:dypgen_keep_data
    ~use_rule_order:dypgen_use_rule_order
    ~use_all_actions:dypgen_use_all_actions
    ~choose_token:dypgen_choose_token lexbuf in
  let aux1 (o,p) = match o with
    | Obj_main r -> (r,p)
    | _ -> failwith "Wrong type for entry result" in
  List.map aux1 pf


let __dypgen_dummy_marker_4 = ()

