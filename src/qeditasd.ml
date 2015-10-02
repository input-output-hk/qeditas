(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Net;;
open Rpc;;
open Setconfig;;

let fallbacknodes = [
"108.61.219.125:20805"
];;

let init_rpcserver pidl =
  Printf.printf "Qeditas server starting\n";
  try
    let s = openlocallistener !Config.rpcport 5 in
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
	Unix.close s2
      with
      | Failure(m) -> Printf.printf "Failure of rpc: %s\n" m
      | _ -> ()
    done;
    Printf.printf "Shutting down Qeditas rpc server.\n";
    Unix.close s;
    Unix.kill pidl 9;
  with
  | _ ->
      Printf.printf "Error. Could not start rpc server. Maybe port %d is temporarily blocked.\n" !Config.rpcport; flush stdout;
      Unix.kill pidl 9;;

let init_connlistener ip =
  try
    let s = openlistener ip !Config.port 5 in
    Printf.printf "Listening for incoming connections.\n"; flush stdout;
    while true do
      try
	let (s2,a2) = Unix.accept s in
	Printf.printf "got conn connection\n"; flush stdout;
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

let pid = Unix.fork();;

if (pid = 0) then
  begin
    process_config_args();
    process_config_file();
    let pidl = Unix.fork() in
    if (pidl = 0) then
      init_conns()
    else
      init_rpcserver pidl
  end;;
