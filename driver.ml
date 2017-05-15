

let print_expression chan expr =
  let doc = Ftal.Lang.p_exp expr in
  PPrintEngine.ToChannel.pretty 0.8 80 chan doc;
  output_string chan "\n";
  flush chan

let handle_expression_file path =
  let expr = Parse.parse_file Parse.expression_eof path in
  print_expression stdout expr

let roundtrip_expression expr =
  let path = "tmp.lamb" in
  let chan = open_out path in
  print_expression chan expr;
  close_out chan;
  handle_expression_file path

let () = handle_expression_file Sys.argv.(1)
