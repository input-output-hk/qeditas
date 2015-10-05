(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Net;;
open Rpc;;
open Setconfig;;

let fallbacknodes = [
"108.61.219.125:20805"
];;

(***
let init_rpcserver pidl =
  Printf.printf "Qeditas server starting\n";
  try
    let lockfn = Filename.concat !Config.datadir "lock" in
    if Sys.file_exists lockfn then
      Printf.printf "Qeditas server seems to already be running. If not, remove lock file by hand.\n"
    else
      begin
	let s = openlocallistener !Config.rpcport 5 in
	let pid = Unix.getpid () in
	let pids = string_of_int pid in
	let lo = open_out lockfn in
	output lo pids 0 (String.length pids);
	close_out lo;
	let cont = ref true in
	while !cont do
	  try
	    Printf.printf "waiting for rpc connection\n"; flush stdout;
	    let (s2,a2) = Unix.accept s in
	    Printf.printf "got rpc connection\n"; flush stdout;
	    let s2in = Unix.in_channel_of_descr s2 in
	    let s2out = Unix.out_channel_of_descr s2 in
	    set_binary_mode_in s2in true;
	    set_binary_mode_out s2out true;
	    let r = rec_rpccom s2in in
	    if r = Stop then
	      cont := false
	    else
	      do_rpccom r s2out;
	    flush s2out;
	    Unix.close s2
	  with
	  | Failure(m) -> Printf.printf "Failure of rpc: %s\n" m
	  | _ -> ()
	done;
	Printf.printf "Shutting down Qeditas rpc server.\n";
	Unix.close s;
	Unix.unlink lockfn
      end;
    List.iter (fun pid -> Unix.kill pid 9) pidl
  with
  | _ ->
      Printf.printf "Error. Could not start rpc server. Maybe port %d is temporarily blocked.\n" !Config.rpcport; flush stdout;
      List.iter (fun pid -> Unix.kill pid 9) pidl

let init_connlistener ip =
  try
    let s = openlistener ip !Config.port 5 in
    Printf.printf "Listening for incoming connections.\n"; flush stdout;
    while true do
      try
	let (s2,a2) = Unix.accept s in
	Printf.printf "got remote connection\n"; flush stdout;
	let s2in = Unix.in_channel_of_descr s2 in
	let s2out = Unix.out_channel_of_descr s2 in
	set_binary_mode_in s2in true;
	set_binary_mode_out s2out true;
	let b0 = input_byte s2in in
	Printf.printf "got conn byte %d\n" b0; flush stdout;
	()
      with _ -> ()
    done
  with _ ->
    Printf.printf "Failed to open a listener for incoming connections. Maybe port %d is temporarily blocked.\n" !Config.port; flush stdout;
    ()

let try_add_node l =
  try
    let (s,si,so) = connectlocal !Config.rpcport in
    send_rpccom so (AddNode(l));
    let by = input_byte si in
    Unix.close s;
    if by = 0 then false else true
  with _ -> false

let find_peers_1 () =
  let fn = Filename.concat !Config.datadir "peers" in
  if Sys.file_exists fn then
    begin
      let succ = ref false in
      let ch = open_in fn in
      try
	while true do
	  let l = input_line ch in
	  try
	    if try_add_node l then
	      succ := true
	  with _ -> () 
	done;
	false
      with End_of_file -> !succ
    end
  else
    false;;

let find_peers_2 () =
  List.iter 
    (fun l -> ignore (try_add_node l))
    fallbacknodes;;

let init_conns () =
  if not (find_peers_1 ()) then find_peers_2 ();
  match !Config.ip with
  | Some(ip) -> init_connlistener ip
  | None ->
      Printf.printf "Not listening for incoming connections.\nIf you want Qeditas to listen for incoming connections set ip to your ip address\nusing ip=... in qeditas.conf or -ip=... on the command line.\n"; flush stdout;
      ();;

let init_staking () =
  try
    ()
  with
  | Failure(m) -> Printf.printf "%s\n" m;
  | _ ->  Printf.printf "Staking process ended\n";;

***)

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
