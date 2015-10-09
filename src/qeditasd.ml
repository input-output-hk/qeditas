(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ctre;;
open Net;;
open Setconfig;;

let fallbacknodes = [
"108.61.219.125:20805"
];;

let conns = ref [];;

let rand_int64 () =
  let r = open_in_bin "/dev/random" in
  let get_byte r = Int64.of_int (input_byte r) in
  let v = Int64.shift_right_logical (get_byte r) 56 in
  let v = Int64.logor v (Int64.shift_right_logical (get_byte r) 48) in
  let v = Int64.logor v (Int64.shift_right_logical (get_byte r) 40) in
  let v = Int64.logor v (Int64.shift_right_logical (get_byte r) 32) in
  let v = Int64.logor v (Int64.shift_right_logical (get_byte r) 24) in
  let v = Int64.logor v (Int64.shift_right_logical (get_byte r) 16) in
  let v = Int64.logor v (Int64.shift_right_logical (get_byte r) 8) in
  let v = Int64.logor v (get_byte r) in
  close_in r;
  v;;

let myaddr () =
  match !Config.ip with
  | Some(ip) -> 
      if !Config.ipv6 then
	"[" ^ ip ^ "]:" ^ (string_of_int !Config.port)
      else
	ip ^ ":" ^ (string_of_int !Config.port)
  | None ->
      "";;

let initialize_conn_accept s =
  if List.length !conns < !Config.maxconns then
    begin
      let sin = Unix.in_channel_of_descr s in
      let sout = Unix.out_channel_of_descr s in
      set_binary_mode_in sin true;
      set_binary_mode_out sout true;
      try
	let m2 = rec_msg_nohang sin 5.0 5.0 in
	match m2 with
	| Some(_,_,Version(vers2,srvs2,tm2,addr_recv2,addr_from2,n2,user_agent2,fr20,fr21,fr22,first_height2,last_height2,relay2,lastchkpt2)) ->
	    send_msg sout Verack;
	    let vers = 1l in
	    let srvs = 1L in
	    let tm = Int64.of_float(Unix.time()) in
	    let nonce = rand_int64() in
	    let user_agent = "Qeditas-Testing-Phase" in
	    let fr0 = RFAll in
	    let fr1 = RFAll in
	    let fr2 = RFAll in
	    let first_height = 0L in
	    let last_height = 0L in
	    let relay = true in
	    let lastchkpt = None in
	    send_msg sout (Version(vers,srvs,tm,addr_from2,myaddr(),nonce,user_agent,fr0,fr1,fr2,first_height,last_height,relay,lastchkpt));
	    let m1 = rec_msg_nohang sin 5.0 5.0 in
	    begin
	      match m1 with
	      | Some(_,_,Verack) ->
		  Printf.printf "Added connection; post handshake\nmy time = %Ld\ntheir time = %Ld\naddr_recv2 = %s\naddr_from2 = %s\n" tm tm2 addr_recv2 addr_from2; flush stdout;
		  let cs =
		    { alive = true;
		      lastmsgtm = Unix.time();
		      pending = [];
		      rframe0 = fr20;
		      rframe1 = fr21;
		      rframe2 = fr22;
		      first_height = first_height2;
		      last_height = last_height2;
		    }
		  in
		  conns := (s,sin,sout,addr_from2,cs)::!conns;
		  true
	      | _ ->
		  Printf.printf "Handshake failed. (No Verack)\n"; flush stdout;
		  Unix.close s;
		  false
	    end
	| _ ->
	    Printf.printf "Handshake failed. (No Version)\n"; flush stdout;
	    Unix.close s; (*** handshake failed ***)
	    false
      with
      | IllformedMsg ->
	  Printf.printf "Handshake failed. (IllformedMsg)\n"; flush stdout;
	  Unix.close s; (*** handshake failed ***)
	  false
    end
  else
    begin
      Printf.printf "Rejecting connection because of maxconns.\n"; flush stdout;
      Unix.close s;
      false
    end;;

let initialize_conn_2 n s sin sout =
  (*** handshake ***)
  let vers = 1l in
  let srvs = 1L in
  let tm = Int64.of_float(Unix.time()) in
  let nonce = rand_int64() in
  let user_agent = "Qeditas-Testing-Phase" in
  let fr0 = RFAll in
  let fr1 = RFAll in
  let fr2 = RFAll in
  let first_height = 0L in
  let last_height = 0L in
  let relay = true in
  let lastchkpt = None in
  send_msg sout (Version(vers,srvs,tm,myaddr(),n,nonce,user_agent,fr0,fr1,fr2,first_height,last_height,relay,lastchkpt));
  try
    let m1 = rec_msg_nohang sin 5.0 5.0 in
    match m1 with
    | Some(_,_,Verack) ->
	begin
	  let m2 = rec_msg_nohang sin 5.0 5.0 in
	  match m2 with
	  | Some(_,_,Version(vers2,srvs2,tm2,addr_recv2,addr_from2,n2,user_agent2,fr20,fr21,fr22,first_height2,last_height2,relay2,lastchkpt2)) ->
	      send_msg sout Verack;
	      Printf.printf "Added connection; post handshake\nmy time = %Ld\ntheir time = %Ld\naddr_recv2 = %s\naddr_from2 = %s\n" tm tm2 addr_recv2 addr_from2; flush stdout;
	      let cs =
		{ alive = true;
		  lastmsgtm = Unix.time();
		  pending = [];
		  rframe0 = fr20;
		  rframe1 = fr21;
		  rframe2 = fr22;
		  first_height = first_height2;
		  last_height = last_height2;
		}
	      in
	      conns := (s,sin,sout,addr_from2,cs)::!conns;
	      true
	  | _ ->
	      Printf.printf "Handshake failed. (No Version)\n"; flush stdout;
	      Unix.close s; (*** handshake failed ***)
	      false
	end
    | _ ->
	begin (*** handshake failed ***)
	  Printf.printf "Handshake failed. (No Verack)\n"; flush stdout;
	  Unix.close s;
	  false
	end
  with
  | IllformedMsg ->
      Printf.printf "Handshake failed. (IllformedMsg)\n"; flush stdout;
      Unix.close s; (*** handshake failed ***)
      false;;

let initialize_conn n s =
  let sin = Unix.in_channel_of_descr s in
  let sout = Unix.out_channel_of_descr s in
  set_binary_mode_in sin true;
  set_binary_mode_out sout true;
  initialize_conn_2 n s sin sout;;

exception Connected;;

let search_for_conns () =
  if !conns = [] then
    begin
      try
	List.iter
	  (fun n ->
	    let (ip,port,v6) = extract_ip_and_port n in
	    if not (!Config.ip = Some(ip) && !Config.ipv6 = v6) then (*** if this is a fallback node, do not connect to itself ***)
	      begin
		try
		  match !Config.socks with
		  | None ->
		      let s = connectpeer ip port in
		      ignore (initialize_conn n s)
		  | Some(4) ->
		      let (s,sin,sout) = connectpeer_socks4 !Config.socksport ip port in
		      ignore (initialize_conn_2 n s sin sout)
		  | Some(5) ->
		      raise (Failure "socks5 is not yet supported")
		  | Some(z) ->
		      raise (Failure ("socks" ^ (string_of_int z) ^ " is not yet supported"))
		with
		| RequestRejected -> Printf.printf "here RequestRejected\n"; flush stdout;
		| Connected -> raise Connected
		| _ -> Printf.printf "here 3\n"; flush stdout;
	      end
	  )
	  fallbacknodes
      with Connected -> ()
    end;;

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
      try
	begin (*** possibly check for a new incomming connection ***)
	  match l with
	  | Some(l) ->
	      begin
		match accept_nohang l 0.1 with
		| Some(s,a) ->
		    begin
		      match a with
		      | Unix.ADDR_UNIX(x) ->
			Printf.printf "got local connection %s\n" x;
		      | Unix.ADDR_INET(x,y) ->
			  Printf.printf "got remote connection %s %d\n" (Unix.string_of_inet_addr x) y;
		    end;
		    flush stdout;
		    if initialize_conn_accept s then
		      Printf.printf "accepted remote connection\n"
		    else
		      Printf.printf "rejected remote connection\n";
		    flush stdout;
		| None -> ()
	      end
	  | None -> ()
	end;
	(*** check each connection for possible messages ***)
	List.iter
	  (fun (s,sin,sout,peeraddr,cs) ->
	    try
	      let tm = Unix.time() in
	      match rec_msg_nohang sin 0.1 1.0 with
	      | None ->
		  begin
		    try
		      ignore (List.find (fun (h,p,tm1,tm2,f) -> p && (tm -. tm2 > 30.0)) cs.pending);
			(*** Something that required a response didn't respond in time (e.g., a Ping).
			     Drop the connection
			 ***)
                      Printf.printf "Ping-Pong failed. Dropping connection.\n"; flush stdout;
                      Unix.close s;
                      cs.alive <- false
                    with Not_found ->
		    if (tm -. cs.lastmsgtm) > 60.0 then (*** If no messages in enough time, send a ping. ***)
		      begin
			Printf.printf "Sending Ping.\n"; flush stdout;
			let mh = send_msg sout Ping in
			Printf.printf "Sent Ping.\n"; flush stdout;
                        cs.pending <- (mh,true,tm,tm,None)::cs.pending;
                        cs.lastmsgtm <- tm
		      end
		  end
	      | Some(replyto,mh,m) ->
		begin
		  Printf.printf "got a msg, new lastmsgtm %f\n" tm; flush stdout;
                  cs.lastmsgtm <- tm;
		  handle_msg sin sout cs replyto mh m
		end
	    with
	    | End_of_file ->
		Printf.printf "Lost connection.\n"; flush stdout;
		cs.alive <- false
	    | IllformedMsg ->
		Printf.printf "IllformedMsg. Breaking connection.\n"; flush stdout;
		cs.alive <- false
	    | exn -> (*** unexpected ***)
		Printf.printf "Other exception: %s\nNot dropping connection yet.\n" (Printexc.to_string exn);
	  )
	  !conns;
	conns := List.filter (fun (s,sin,sout,peeraddr,cs) -> cs.alive) !conns
      with _ -> () (*** ensuring no exception escapes the main loop ***)
    done
  end;;

main ();;
