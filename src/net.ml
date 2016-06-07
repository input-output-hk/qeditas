(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Utils
open Ser
open Hashaux
open Hash

type msgtype =
  | Version
  | Verack
  | Addr
  | Inv
  | GetData
  | MNotFound
  | GetSTxs
  | GetTxs
  | GetTxSignatures
  | GetBlocks
  | GetBlockdeltas
  | GetBlockdeltahs
  | GetHeaders
  | MSTx
  | MTx
  | MTxSignature
  | MBlock
  | Headers
  | MBlockdelta
  | MBlockdeltah
  | GetAddr
  | Mempool
  | Alert
  | Ping
  | Pong
  | Reject
  | GetCTreeElement
  | GetHConsElement
  | GetAsset
  | CTreeElement
  | HConsElement
  | Asset
  | Checkpoint
  | AntiCheckpoint

let msgtype_of_int i =
  try
    List.nth
      [Version;Verack;Addr;Inv;GetData;MNotFound;GetSTxs;GetTxs;GetTxSignatures;
       GetBlocks;GetBlockdeltas;GetBlockdeltahs;GetHeaders;MSTx;MTx;MTxSignature;MBlock;
       Headers;MBlockdelta;MBlockdeltah;GetAddr;Mempool;Alert;Ping;Pong;Reject;
       GetCTreeElement;GetHConsElement;GetAsset;CTreeElement;HConsElement;Asset;
       Checkpoint;AntiCheckpoint]
      i
  with Failure("nth") -> raise Not_found

let int_of_msgtype mt =
  match mt with
  | Version -> 0
  | Verack -> 1
  | Addr -> 2
  | Inv -> 3
  | GetData -> 4
  | MNotFound -> 5
  | GetSTxs -> 6
  | GetTxs -> 7
  | GetTxSignatures -> 8
  | GetBlocks -> 9
  | GetBlockdeltas -> 10
  | GetBlockdeltahs -> 11
  | GetHeaders -> 12
  | MSTx -> 13
  | MTx -> 14
  | MTxSignature -> 15
  | MBlock -> 16
  | Headers -> 17
  | MBlockdelta -> 18
  | MBlockdeltah -> 19
  | GetAddr -> 20
  | Mempool -> 21
  | Alert -> 22
  | Ping -> 23
  | Pong -> 24
  | Reject -> 25
  | GetCTreeElement -> 26
  | GetHConsElement -> 27
  | GetAsset -> 28
  | CTreeElement -> 29
  | HConsElement -> 30
  | Asset -> 31
  | Checkpoint -> 32
  | AntiCheckpoint -> 33

let myaddr () =
  match !Config.ip with
  | Some(ip) -> 
      if !Config.ipv6 then
	"[" ^ ip ^ "]:" ^ (string_of_int !Config.port)
      else
	ip ^ ":" ^ (string_of_int !Config.port)
  | None ->
      ""

let fallbacknodes = [
"172.246.252.93:20805"
]

let testnetfallbacknodes = [
"172.246.252.93:20804"
]

let getfallbacknodes () =
  if !Config.testnet then
    testnetfallbacknodes
  else
    fallbacknodes

let knownpeers : (string,int64) Hashtbl.t = Hashtbl.create 1000

let addknownpeer lasttm n =
  if not (n = "") && not (n = myaddr()) && not (List.mem n (getfallbacknodes())) then
    try
      let oldtm = Hashtbl.find knownpeers n in
      Hashtbl.replace knownpeers n lasttm
    with Not_found ->
      let peerfn = Filename.concat !Config.datadir (if !Config.testnet then "testnet/peers" else "peers") in
      if Sys.file_exists peerfn then
	let s = open_out_gen [Open_append;Open_wronly] 0x644 peerfn in
	output_string s n;
	output_char s '\n';
	output_string s (Int64.to_string lasttm);
	output_char s '\n';
	close_out s
      else
	let s = open_out peerfn in
	output_string s n;
	output_char s '\n';
	output_string s (Int64.to_string lasttm);
	output_char s '\n';
	close_out s

let getknownpeers () =
  let cnt = ref 0 in
  let peers = ref [] in
  let currtm = Int64.of_float (Unix.time()) in
  Hashtbl.iter (fun n lasttm -> if !cnt < 1000 && Int64.sub currtm lasttm < 604800L then (incr cnt; peers := n::!peers)) knownpeers;
  !peers

let loadknownpeers () =
  let currtm = Int64.of_float (Unix.time()) in
  let peerfn = Filename.concat !Config.datadir (if !Config.testnet then "testnet/peers" else "peers") in
  if Sys.file_exists peerfn then
    let s = open_in peerfn in
    try
      while true do
	let n = input_line s in
	let lasttm = Int64.of_string (input_line s) in
	if Int64.sub currtm lasttm < 604800L then
	  Hashtbl.add knownpeers n lasttm
      done
    with End_of_file -> ()

let saveknownpeers () =
  let peerfn = Filename.concat !Config.datadir (if !Config.testnet then "testnetpeers" else "peers") in
  let s = open_out_gen [Open_append;Open_wronly;Open_trunc] 0x644 peerfn in
  Hashtbl.iter
    (fun n lasttm ->
      output_string s n;
      output_char s '\n';
      output_string s (Int64.to_string lasttm);
      output_char s '\n')
    knownpeers;
  close_out s

exception GettingRemoteData
exception RequestRejected
exception IllformedMsg
exception ProtocolViolation of string
exception SelfConnection

let openlistener ip port numconns =
  let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  let ia = Unix.inet_addr_of_string ip in
  Unix.bind s (Unix.ADDR_INET(ia, port));
  Unix.listen s numconns;
  s

let connectpeer ip port =
  let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  let ia = Unix.inet_addr_of_string ip in
  Unix.connect s (Unix.ADDR_INET(ia, port));
  s

let extract_ipv4 ip =
  let x = Array.make 4 0 in
  let j = ref 0 in
  for i = 0 to String.length ip - 1 do
    let c = Char.code ip.[i] in
    if c = 46 && !j < 3 then
      incr j
    else if c >= 48 && c < 58 then
      x.(!j) <- x.(!j) * 10 + (c-48)
    else
      raise (Failure "Not an ipv4 address")
  done;
  (x.(0),x.(1),x.(2),x.(3))

let rec extract_ipv4_and_port ipp i l =
  if i+2 < l then
    if ipp.[i] = ':' then
      (String.sub ipp 0 i,int_of_string (String.sub ipp (i+1) (l-(i+1))))
    else
      extract_ipv4_and_port ipp (i+1) l
  else
    raise (Failure "not an ipv4 address with a port number")

let rec extract_ipv6_and_port ipp i l =
  if i+3 < l then
    if ipp.[i] = ']' then
      if ipp.[i+1] = ':' then
	(String.sub ipp 0 i,int_of_string (String.sub ipp (i+2) (l-(i+2))))
      else
	raise (Failure "not an ipv4 address with a port number")
    else
      extract_ipv6_and_port ipp (i+1) l
  else
    raise (Failure "not an ipv6 address with a port number")

let extract_ip_and_port ipp =
  let l = String.length ipp in
  if l = 0 then
    raise (Failure "Not an ip address with a port number")
  else if ipp.[0] = '[' then
    let (ip,port) = extract_ipv6_and_port ipp 1 l in
    (ip,port,true)
  else
    let (ip,port) = extract_ipv4_and_port ipp 0 l in
    (ip,port,false)

let connectpeer_socks4 proxyport ip port =
  let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.connect s (Unix.ADDR_INET(Unix.inet_addr_loopback, proxyport));
  let sin = Unix.in_channel_of_descr s in
  let sout = Unix.out_channel_of_descr s in
  set_binary_mode_in sin true;
  set_binary_mode_out sout true;
  output_byte sout 4;
  output_byte sout 1;
  (** port, big endian **)
  output_byte sout ((port asr 8) land 255);
  output_byte sout (port land 255);
  (** ip **)
  let (x0,x1,x2,x3) = extract_ipv4 ip in
  output_byte sout x0;
  output_byte sout x1;
  output_byte sout x2;
  output_byte sout x3;
  output_byte sout 0;
  flush sout;
  let z = input_byte sin in
  let cd = input_byte sin in
  Printf.fprintf !log "%d %d\n" z cd; flush !log;
  if not (cd = 90) then raise RequestRejected;
  for i = 1 to 6 do
    ignore (input_byte sin)
  done;
  (s,sin,sout)

type connstate = {
    conntime : float;
    realaddr : string;
    mutable handshakestep : int;
    mutable peertimeskew : int;
    mutable protvers : int32;
    mutable useragent : string;
    mutable addrfrom : string;
    mutable locked : bool;
    mutable lastmsgtm : float;
    mutable pending : (hashval * (bool * float * float * (msgtype * string -> unit))) list;
    mutable sentinv : (int * hashval) list;
    mutable rinv : (int * hashval) list;
    mutable invreq : (int * hashval) list;
    mutable first_header_height : int64; (*** how much header history is stored at the node ***)
    mutable first_full_height : int64; (*** how much block/ctree history is stored at the node ***)
    mutable last_height : int64; (*** how up to date the node is ***)
  }

let send_msg_real c replyto mt ms =
  let magic = if !Config.testnet then 0x51656454l else 0x5165644dl in
  let msl = String.length ms in
  (*** Magic Number for mainnet: QedM ***)
  seocf (seo_int32 seoc magic (c,None));
  begin
    match replyto with
    | None ->
	output_byte c 0
    | Some(h) ->
	output_byte c 1;
	seocf (seo_hashval seoc h (c,None))
  end;
  output_byte c (int_of_msgtype mt);
  seocf (seo_int32 seoc (Int32.of_int msl) (c,None));
  let mh = hash160 ms in
  seocf (seo_hashval seoc mh (c,None));
  for j = 0 to msl-1 do
    output_byte c (Char.code ms.[j])
  done;
  flush c;
  mh

let send_msg c mt m = send_msg_real c None mt m
let send_reply c h mt m = send_msg_real c (Some(h)) mt m

(***
 Throw IllformedMsg if something's wrong with the format or if it reads the first byte but times out before reading the full message.
 If IllformedMsg is thrown, the connection should be severed.
 ***)
let rec_msg c =
  let (mag0,mag1,mag2,mag3) = if !Config.testnet then (0x51,0x65,0x64,0x54) else (0x51,0x65,0x64,0x4d) in
  let by0 = input_byte c in
  if not (by0 = mag0) then raise IllformedMsg;
  try
    let by1 = input_byte c in
    if not (by1 = mag1) then raise IllformedMsg;
    let by2 = input_byte c in
    if not (by2 = mag2) then raise IllformedMsg;
    let by3 = input_byte c in
    if not (by3 = mag3) then raise IllformedMsg;
    let replyto =
      let by4 = input_byte c in
      if by4 = 0 then (*** not a reply ***)
	None
      else if by4 = 1 then
	let (h,_) = sei_hashval seic (c,None) in
	(Some(h))
      else
	raise IllformedMsg
    in
    let mt =
      try
	msgtype_of_int (input_byte c)
      with Not_found -> raise IllformedMsg
    in
    let (msl,_) = sei_int32 seic (c,None) in
    if msl > 67108863l then raise IllformedMsg;
    let msl = Int32.to_int msl in
    let (mh,_) = sei_hashval seic (c,None) in
    let sb = Buffer.create msl in
    for j = 0 to msl-1 do
      let by = input_byte c in
      Buffer.add_char sb (Char.chr by)
    done;
    let ms = Buffer.contents sb in
    if not (mh = hash160 ms) then raise IllformedMsg;
    (replyto,mh,mt,ms)
  with
  | _ -> (*** consider it an IllformedMsg no matter what the exception raised was ***)
      raise IllformedMsg

let netlistenerth : Thread.t option ref = ref None
let netseekerth : Thread.t option ref = ref None
let netconns : (Thread.t * (Unix.file_descr * in_channel * out_channel * connstate option ref)) list ref = ref []
let this_nodes_nonce = ref 0L

let peeraddr gcs =
  match gcs with
  | Some(cs) -> cs.addrfrom
  | None -> "[dead]"

let log_msg m =
  let h = string_hexstring m in
  Printf.fprintf !log "\nmsg: %s\n" h

let network_time () =
  let mytm = Int64.of_float (Unix.time()) in
  let offsets = ref [] in
  List.iter (fun (_,(_,_,_,gcs)) -> match !gcs with Some(cs) -> offsets := List.merge compare [cs.peertimeskew] !offsets | None -> ()) !netconns;
  if !offsets = [] then
    (mytm,0)
  else
    let m = (List.length !offsets) lsr 1 in
    let mskew = List.nth !offsets m in
    (Int64.add mytm (Int64.of_int mskew),mskew)

let handle_msg replyto mt sin sout cs mh m =
  match replyto with
  | Some(h) ->
      begin
	try
	  let (b,tm1,tm2,f) = List.assoc h cs.pending in
	  cs.pending <- List.filter (fun (k,_) -> not (h = k)) cs.pending;
	  f(mt,m)
	with Not_found -> () (*** Reply to unknown request, ignore for now ***)
      end
  | None ->
      match mt with
      | _ -> raise (Failure "unwritten; to do")

let connlistener (s,sin,sout,gcs) =
  try
    while true do
      try
	let (replyto,mh,mt,m) = rec_msg sin in
	match !gcs with
	| Some(cs) -> cs.lastmsgtm <- Unix.time(); handle_msg replyto mt sin sout cs mh m
	| None -> raise End_of_file (*** connection died; this probably shouldn't happen, as we should have left this thread when it died ***)
      with
      | Unix.Unix_error(c,x,y) -> (*** close connection ***)
	  Printf.fprintf !log "Unix error exception raised in connection listener for %s:\n%s %s %s\nClosing connection\n" (peeraddr !gcs) (Unix.error_message c) x y;
	  flush !log;
	  Unix.close s;
	  raise Exit
      | End_of_file -> (*** close connection ***)
	  Printf.fprintf !log "Channel for connection %s raised End_of_file. Closing connection\n" (peeraddr !gcs);
	  flush !log;
	  Unix.close s;
	  raise Exit
      | ProtocolViolation(x) -> (*** close connection ***)
	  Printf.fprintf !log "Protocol violation by connection %s: %s\nClosing connection\n" (peeraddr !gcs) x;
	  flush !log;
	  Unix.close s;
	  raise Exit
      | SelfConnection -> (*** detected a self-connection attempt, close ***)
	  Printf.fprintf !log "Stopping potential self-connection\n";
	  flush !log;
	  Unix.close s;
	  raise Exit
      | exc -> (*** report but ignore all other exceptions ***)
	  Printf.fprintf !log "Ignoring exception raised in connection listener for %s:\n%s\n" (peeraddr !gcs) (Printexc.to_string exc);
	  flush !log;
    done
  with _ -> gcs := None (*** indicate that the connection is dead; it will be removed from netaddr by the netlistener or netseeker ***)

let remove_dead_conns () =
  (*** should lock netconns ***)
  netconns := List.filter (fun (_,(_,_,_,gcs)) -> match !gcs with Some(_) -> true | None -> false) !netconns
  (*** should unlock netconns ***)

exception EnoughConnections

let initialize_conn_accept ra s =
  if List.length !netconns < !Config.maxconns then
    begin
      let sin = Unix.in_channel_of_descr s in
      let sout = Unix.out_channel_of_descr s in
      set_binary_mode_in sin true;
      set_binary_mode_out sout true;
      let tm = Unix.time() in
      let cs = { conntime = tm; realaddr = ra; handshakestep = 1; peertimeskew = 0; protvers = Version.protocolversion; useragent = ""; addrfrom = ""; locked = false; lastmsgtm = tm; pending = []; sentinv = []; rinv = []; invreq = []; first_header_height = 0L; first_full_height = 0L; last_height = 0L } in
      let sgcs = (s,sin,sout,ref (Some(cs))) in
      let cth = Thread.create connlistener sgcs in
      (* should lock netconns *)
      netconns := (cth,sgcs)::!netconns;
      (* should unlock netconns *)
    end
  else
    begin
      Unix.close s;
      raise EnoughConnections
    end

let initialize_conn_2 n s sin sout =
  Printf.fprintf !log "calling 2\n"; flush !log;
  (*** initiate handshake ***)
  let vers = 1l in
  let srvs = 1L in
  let tm = Unix.time() in
  let fhh = 0L in
  let ffh = 0L in
  let lh = 0L in
  let relay = true in
  let lastchkpt = None in
  let vm = Buffer.create 100 in
  seosbf
    (seo_prod
       (seo_prod6 seo_int32 seo_int64 seo_int64 seo_string seo_string seo_int64)
       (seo_prod6 seo_string seo_int64 seo_int64 seo_int64 seo_bool (seo_option (seo_prod seo_int64 seo_hashval)))
       seosb
       ((vers,srvs,Int64.of_float tm,n,myaddr(),!this_nodes_nonce),
	(Version.useragent,fhh,ffh,lh,relay,lastchkpt))
       (vm,None));
  send_msg sout Version (Buffer.contents vm);
  let cs = { conntime = tm; realaddr = n; handshakestep = 2; peertimeskew = 0; protvers = Version.protocolversion; useragent = ""; addrfrom = ""; locked = false; lastmsgtm = tm; pending = []; sentinv = []; rinv = []; invreq = []; first_header_height = fhh; first_full_height = ffh; last_height = lh } in
  let sgcs = (s,sin,sout,ref (Some(cs))) in
  let cth = Thread.create connlistener sgcs in
  (* should lock netconns *)
  netconns := (cth,sgcs)::!netconns
  (* should unlock netconns *)

let initialize_conn n s =
  let sin = Unix.in_channel_of_descr s in
  let sout = Unix.out_channel_of_descr s in
  set_binary_mode_in sin true;
  set_binary_mode_out sout true;
  initialize_conn_2 n s sin sout

let tryconnectpeer n =
  if List.length !netconns >= !Config.maxconns then raise EnoughConnections;
  try
    ignore (List.find (fun (_,(_,_,_,gcs)) -> n = peeraddr !gcs) !netconns);
  with Not_found ->
    let (ip,port,v6) = extract_ip_and_port n in
    begin
      try
	match !Config.socks with
	| None ->
	    let s = connectpeer ip port in
	    ignore (initialize_conn n s)
	| Some(4) ->
	    let (s,sin,sout) = connectpeer_socks4 !Config.socksport ip port in
	    ignore (initialize_conn_2 n s sin sout);
	| Some(5) ->
	    raise (Failure "socks5 is not yet supported")
	| Some(z) ->
	    raise (Failure ("socks" ^ (string_of_int z) ^ " is not yet supported"))
      with
      | RequestRejected ->
	  Printf.fprintf !log "RequestRejected\n"; flush !log;
      | _ ->
	  ()
    end

let netlistener l =
  while true do
    try
      let (s,a) = Unix.accept l in
      let ra =
	begin
	  match a with
	  | Unix.ADDR_UNIX(x) ->
	      Printf.fprintf !log "got local connection %s\n" x;
	      flush !log;
	      "local " ^ x
	  | Unix.ADDR_INET(x,y) ->
	      Printf.fprintf !log "got remote connection %s %d\n" (Unix.string_of_inet_addr x) y;
	      flush !log;
	      (Unix.string_of_inet_addr x) ^ " " ^ (string_of_int y)
	end
      in
      flush !log;
      remove_dead_conns();
      initialize_conn_accept ra s
    with
    | EnoughConnections -> Printf.fprintf !log "Rejecting connection because of maxconns.\n"; flush !log;
    | _ -> ()
  done

let netseeker_loop () =
  while true do
    try
      remove_dead_conns();
      if List.length !netconns < max 1 (!Config.maxconns lsr 1) then
	begin
	  Hashtbl.iter
	    (fun n oldtm ->
	      try (*** don't connect to the same peer twice ***)
		ignore (List.find
			  (fun (_,(_,_,_,gcs)) -> peeraddr !gcs = n)
			  !netconns)
	      with Not_found -> tryconnectpeer n
	      )
	    knownpeers
	end;
      if !netconns = [] then
	begin
	  List.iter
	    (fun n -> tryconnectpeer n)
	    (if !Config.testnet then testnetfallbacknodes else fallbacknodes)
	end;
      Unix.sleep 600;
    with
    | _ -> ()
  done

let netseeker () =
  loadknownpeers();
  netseekerth := Some(Thread.create netseeker_loop ())

