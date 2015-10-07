(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Net;;
open Setconfig;;

let fallbacknodes = [
"108.61.219.125:20805"
];;

let conns = ref [];;

let initialize_conn_2 s sin sout =
  if List.length !conns < 10 then (*** Should be Config.maxconns ***)
    begin
      output_byte sout 1; (*** connection accepted ***)
      (*** handshake, empty for now ***)
      flush sout;
      conns := (s,sin,sout,Buffer.create 100,ref true)::!conns
    end
  else
    begin
      output_byte sout 0; (*** connection rejected ***)
      flush sout;
      Unix.close s
    end;;

let initialize_conn s =
  let sin = Unix.in_channel_of_descr s in
  let sout = Unix.out_channel_of_descr s in
  set_binary_mode_in sin true;
  set_binary_mode_out sout true;
  initialize_conn_2 s sin sout;;

let search_for_conns () =
  if !conns = [] then
    List.iter
      (fun n ->
	let (ip,port) = extract_ip_and_port n in
	if not (!Config.ip = Some(ip)) then (*** if this is a fallback node, do not connect to itself ***)
	  begin
	    try
	      match !Config.socks with
	      | None ->
		  let s = connectpeer ip port in
		  initialize_conn s
	      | Some(4) ->
		  Printf.printf "here 1\n"; flush stdout;
		  let (s,sin,sout) = connectpeer_socks4 !Config.socksport ip port in
		  Printf.printf "here 2\n"; flush stdout;
		  initialize_conn_2 s sin sout
	      | Some(5) -> () (*** to do ***)
	      | _ -> ()
	    with
	    | RequestRejected -> Printf.printf "here RequestRejected\n"; flush stdout;
	    | _ -> Printf.printf "here 3\n"; flush stdout;
	  end
	)
      fallbacknodes;;

let main () =
  begin
    process_config_args();
    process_config_file();
    let l = 
      match !Config.ip with
      | Some(ip) ->
	  let l = openlistener ip !Config.port 5 in
	  Printf.printf "Listening for incoming connections.\n";
	  flush stdout;
	  Some(l)
      | None ->
	  Printf.printf "Not listening for incoming connections.\nIf you want Qeditas to listen for incoming connections set ip to your ip address\nusing ip=... in qeditas.conf or -ip=... on the command line.\n";
	  flush stdout;
	  None
    in
    sethungsignalhandler();
    search_for_conns ();
    while true do (*** main process loop ***)
      begin (*** possibly check for a new incomming connection ***)
	match l with
	| Some(l) ->
	    begin
	      match accept_nohang l 0.1 with
	      | Some(s,a) ->
		  Printf.printf "got remote connection\n";
		  flush stdout;
		  initialize_conn s
	      | None -> ()
	    end
	| None -> ()
      end;
      (*** check each connection for a possible message ***)
      List.iter
	(fun (s,sin,sout,sb,alive) ->
	  try
	    match input_byte_nohang sin 0.1 with
	    | Some(b) -> Printf.printf "got %d\n" b; flush stdout; Buffer.add_char sb (Char.chr b) (*** oversimplified, need to know when the message ended in real version; also should keep reading as long as there is time and input ***)
	    | None -> ()
	  with _ -> alive := false
	)
	!conns;
      conns := List.filter (fun (s,sin,sout,sb,alive) -> !alive) !conns
    done
  end;;

main ();;
