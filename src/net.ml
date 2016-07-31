(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Utils
open Ser
open Hashaux
open Hash

let netblkh : int64 ref = ref 0L

type msgtype =
  | Version
  | Verack
  | Addr
  | Inv
  | GetData
  | MNotFound
  | GetSTx
  | GetTx
  | GetTxSignatures
  | GetHeader
  | GetHeaders
  | GetBlock
  | GetBlockdelta
  | GetBlockdeltah
  | STx
  | Tx
  | TxSignatures
  | Block
  | Headers
  | Blockdelta
  | Blockdeltah
  | GetAddr
  | Mempool
  | Alert
  | Ping
  | Pong
  | Reject
  | GetCTreeElement
  | GetHConsElement
  | GetAsset
  | GetAssetH
  | CTreeElement
  | HConsElement
  | Asset
  | AssetH
  | Checkpoint
  | AntiCheckpoint
  | NewHeader

let msgtype_of_int i =
  try
    List.nth
      [Version;Verack;Addr;Inv;GetData;MNotFound;GetSTx;GetTx;GetTxSignatures;
       GetBlock;GetBlockdelta;GetBlockdeltah;GetHeader;STx;Tx;TxSignatures;Block;
       Headers;Blockdelta;Blockdeltah;GetAddr;Mempool;Alert;Ping;Pong;Reject;
       GetCTreeElement;GetHConsElement;GetAsset;CTreeElement;HConsElement;Asset;
       Checkpoint;AntiCheckpoint;NewHeader;GetHeaders;GetAssetH;AssetH]
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
  | GetSTx -> 6
  | GetTx -> 7
  | GetTxSignatures -> 8
  | GetBlock -> 9
  | GetBlockdelta -> 10
  | GetBlockdeltah -> 11
  | GetHeader -> 12
  | STx -> 13
  | Tx -> 14
  | TxSignatures -> 15
  | Block -> 16
  | Headers -> 17
  | Blockdelta -> 18
  | Blockdeltah -> 19
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
  | NewHeader -> 34
  | GetHeaders -> 35
  | GetAssetH -> 36
  | AssetH -> 37

let string_of_msgtype mt =
  match mt with
  | Version -> "Version"
  | Verack -> "Verack"
  | Addr -> "Addr"
  | Inv -> "Inv"
  | GetData -> "GetData"
  | MNotFound -> "MNotFound"
  | GetSTx -> "GetSTx"
  | GetTx -> "GetTx"
  | GetTxSignatures -> "GetTxSignatures"
  | GetBlock -> "GetBlock"
  | GetBlockdelta -> "GetBlockdelta"
  | GetBlockdeltah -> "GetBlockdeltah"
  | GetHeader -> "GetHeader"
  | GetHeaders -> "GetHeaders"
  | STx -> "STx"
  | Tx -> "Tx"
  | TxSignatures -> "TxSignatures"
  | Block -> "Block"
  | Headers -> "Headers"
  | Blockdelta -> "Blockdelta"
  | Blockdeltah -> "Blockdeltah"
  | GetAddr -> "GetAddr"
  | Mempool -> "Mempool"
  | Alert -> "Alert"
  | Ping -> "Ping"
  | Pong -> "Pong"
  | Reject -> "Reject"
  | GetCTreeElement -> "GetCTreeElement"
  | GetHConsElement -> "GetHConsElement"
  | GetAsset -> "GetAsset"
  | GetAssetH -> "GetAssetH"
  | CTreeElement -> "CTreeElement"
  | HConsElement -> "HConsElement"
  | Asset -> "Asset"
  | AssetH -> "AssetH"
  | Checkpoint -> "Checkpoint"
  | AntiCheckpoint -> "AntiCheckpoint"
  | NewHeader -> "NewHeader"

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
(* ":20805" *)
]

let testnetfallbacknodes = [
 "108.61.219.125:20804"
(* ":20804" *)
]

let getfallbacknodes () =
  if !Config.testnet then
    testnetfallbacknodes
  else
    fallbacknodes

exception BannedPeer
let bannedpeers : (string,unit) Hashtbl.t = Hashtbl.create 1000
let banpeer n = Hashtbl.add bannedpeers n ()
let clearbanned () = Hashtbl.clear bannedpeers

let knownpeers : (string,int64) Hashtbl.t = Hashtbl.create 1000

let addknownpeer lasttm n =
  if not (n = "") && not (n = myaddr()) && not (List.mem n (getfallbacknodes())) && not (Hashtbl.mem bannedpeers n) then
    try
      let oldtm = Hashtbl.find knownpeers n in
      Hashtbl.replace knownpeers n lasttm
    with Not_found ->
      Hashtbl.add knownpeers n lasttm;
      let peerfn = Filename.concat (if !Config.testnet then Filename.concat !Config.datadir "testnet" else !Config.datadir) "peers" in
      if Sys.file_exists peerfn then
	let s = open_out_gen [Open_append;Open_wronly] 0o644 peerfn in
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

let removeknownpeer n =
  if not (n = "") && not (n = myaddr()) && not (List.mem n (getfallbacknodes())) then
    Hashtbl.remove knownpeers n

let getknownpeers () =
  let cnt = ref 0 in
  let peers = ref [] in
  let currtm = Int64.of_float (Unix.time()) in
  Hashtbl.iter (fun n lasttm -> if !cnt < 1000 && Int64.sub currtm lasttm < 604800L then (incr cnt; peers := n::!peers)) knownpeers;
  !peers

let loadknownpeers () =
  let currtm = Int64.of_float (Unix.time()) in
  let peerfn = Filename.concat (if !Config.testnet then Filename.concat !Config.datadir "testnet" else !Config.datadir) "peers" in
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
  let peerfn = Filename.concat (if !Config.testnet then Filename.concat !Config.datadir "testnet" else !Config.datadir) "peers" in
  let s = open_out peerfn in
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
  if not (cd = 90) then raise RequestRejected;
  for i = 1 to 6 do
    ignore (input_byte sin)
  done;
  (s,sin,sout)

type connstate = {
    conntime : float;
    realaddr : string;
    connmutex : Mutex.t;
    sendqueue : (hashval * hashval option * msgtype * string) Queue.t;
    sendqueuenonempty : Condition.t;
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

let send_inv_fn : (int -> out_channel -> connstate -> unit) ref = ref (fun _ _ _ -> ())
let msgtype_handler : (msgtype,in_channel * out_channel * connstate * string -> unit) Hashtbl.t = Hashtbl.create 50

let send_msg c mh replyto mt ms =
  let magic = if !Config.testnet then 0x51656454l else 0x5165644dl in (*** Magic Number for testnet: QedT and for mainnet: QedM ***)
  let msl = String.length ms in
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
  seocf (seo_hashval seoc mh (c,None));
  for j = 0 to msl-1 do
    output_byte c (Char.code ms.[j])
  done;
  flush c

let queue_msg_real cs replyto mt m =
  let mh = hash160 m in
  Mutex.lock cs.connmutex;
  Queue.add (mh,replyto,mt,m) cs.sendqueue;
  Mutex.unlock cs.connmutex;
  Condition.signal cs.sendqueuenonempty;
  mh

let queue_msg cs mt m = queue_msg_real cs None mt m
let queue_reply cs h mt m = queue_msg_real cs (Some(h)) mt m

(***
 Throw IllformedMsg if something's wrong with the format or if it reads the first byte but times out before reading the full message.
 If IllformedMsg is thrown, the connection should be severed.
 ***)
let rec_msg blkh c =
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
    if msl > Int32.of_int (maxblockdeltasize blkh) then raise IllformedMsg;
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
let netconns : (Thread.t * Thread.t * (Unix.file_descr * in_channel * out_channel * connstate option ref)) list ref = ref []
let netconnsmutex : Mutex.t = Mutex.create()
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
  List.iter (fun (_,_,(_,_,_,gcs)) -> match !gcs with Some(cs) -> offsets := List.merge compare [cs.peertimeskew] !offsets | None -> ()) !netconns;
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
      if cs.handshakestep < 5 then
	begin
	  match mt with
	  | Version ->
	      let (((vers,srvs,tm,addr_recv,addr_from,n),(ua,fhh,ffh,lh,relay,lastchkpt)),_) =
		sei_prod
		  (sei_prod6 sei_int32 sei_int64 sei_int64 sei_string sei_string sei_int64)
		  (sei_prod6 sei_string sei_int64 sei_int64 sei_int64 sei_bool (sei_option (sei_prod sei_int64 sei_hashval)))
		  seis (m,String.length m,None,0,0)
	      in
	      begin
		if n = !this_nodes_nonce then
		  raise SelfConnection
		else
		  let minvers = if vers > Version.protocolversion then Version.protocolversion else 0l in
		  let mytm = Int64.of_float (Unix.time()) in
		  let tmskew = Int64.sub tm mytm in
		  if tmskew > 7200L then
		    raise (ProtocolViolation("Peer rejected due to excessive time skew"))
		  else
		    let tmskew = Int64.to_int tmskew in
		    if cs.handshakestep = 1 then
		      begin
			ignore (queue_msg cs Verack "");
			let vm = Buffer.create 100 in
			seosbf
			  (seo_prod
			     (seo_prod6 seo_int32 seo_int64 seo_int64 seo_string seo_string seo_int64)
			     (seo_prod6 seo_string seo_int64 seo_int64 seo_int64 seo_bool (seo_option (seo_prod seo_int64 seo_hashval)))
			     seosb
			     ((minvers,0L,mytm,addr_from,myaddr(),!this_nodes_nonce),
			      (Version.useragent,0L,0L,0L,true,None))
			     (vm,None));
			queue_msg cs Version (Buffer.contents vm);
			cs.handshakestep <- 3;
			cs.peertimeskew <- tmskew;
			cs.useragent <- ua;
			cs.protvers <- minvers;
			cs.addrfrom <- addr_from;
			cs.first_header_height <- fhh;
			cs.first_full_height <- ffh;
			cs.last_height <- lh;
		      end
		    else if cs.handshakestep = 4 then
		      begin
			queue_msg cs Verack "";
			cs.handshakestep <- 5;
			cs.peertimeskew <- tmskew;
			cs.useragent <- ua;
			cs.protvers <- minvers;
			cs.addrfrom <- addr_from;
			cs.first_header_height <- fhh;
			cs.first_full_height <- ffh;
			cs.last_height <- lh;
			!send_inv_fn 5000 sout cs
		      end
		    else
		      raise (ProtocolViolation "Handshake failed")
	      end
	  | Verack ->
	      begin
		if cs.handshakestep = 2 then
		  cs.handshakestep <- 4
		else if cs.handshakestep = 3 then
		  begin
		    cs.handshakestep <- 5;
		    !send_inv_fn 5000 sout cs
		  end
		else
		  raise (ProtocolViolation("Unexpected Verack"))
	      end
	  | _ -> raise (ProtocolViolation "Handshake failed")
	end
      else
      try
	let f = Hashtbl.find msgtype_handler mt in
	f(sin,sout,cs,m)
      with Not_found ->
	match mt with
	| Version -> raise (ProtocolViolation "Version message after handshake")
	| Verack -> raise (ProtocolViolation "Verack message after handshake")
	| _ -> raise (Failure ("No handler found for message type " ^ (string_of_msgtype mt)))

let connlistener (s,sin,sout,gcs) =
  try
    while true do
      try
	let (replyto,mh,mt,m) = rec_msg !netblkh sin in
	match !gcs with
	| Some(cs) ->
	    let tm = Unix.time() in
	    cs.lastmsgtm <- tm;
	    if Hashtbl.mem knownpeers cs.addrfrom then Hashtbl.replace knownpeers cs.addrfrom (Int64.of_float tm);
	    handle_msg replyto mt sin sout cs mh m
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

let connsender (s,sin,sout,gcs) =
  try
    while true do
      try
	match !gcs with
	| Some(cs) ->
	    begin
	      try
		Mutex.lock cs.connmutex;
		while true do
		  let (mh,replyto,mt,m) = Queue.take cs.sendqueue in
		  send_msg sout mh replyto mt m
		done;
		Mutex.unlock cs.connmutex;
	      with
	      | _ ->
		  Condition.wait cs.sendqueuenonempty cs.connmutex;
		  Mutex.unlock cs.connmutex;
	    end
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
  Mutex.lock netconnsmutex;
  netconns := List.filter (fun (_,_,(_,_,_,gcs)) -> match !gcs with Some(_) -> true | None -> false) !netconns;
  Mutex.unlock netconnsmutex

exception EnoughConnections

let initialize_conn_accept ra s =
  if List.length !netconns < !Config.maxconns then
    begin
      let sin = Unix.in_channel_of_descr s in
      let sout = Unix.out_channel_of_descr s in
      set_binary_mode_in sin true;
      set_binary_mode_out sout true;
      let tm = Unix.time() in
      let cs = { conntime = tm; realaddr = ra; connmutex = Mutex.create(); sendqueue = Queue.create(); sendqueuenonempty = Condition.create(); handshakestep = 1; peertimeskew = 0; protvers = Version.protocolversion; useragent = ""; addrfrom = ""; locked = false; lastmsgtm = tm; pending = []; sentinv = []; rinv = []; invreq = []; first_header_height = 0L; first_full_height = 0L; last_height = 0L } in
      let sgcs = (s,sin,sout,ref (Some(cs))) in
      let clth = Thread.create connlistener sgcs in
      let csth = Thread.create connsender sgcs in
      Mutex.lock netconnsmutex;
      netconns := (clth,csth,sgcs)::!netconns;
      Mutex.unlock netconnsmutex
    end
  else
    begin
      Unix.close s;
      raise EnoughConnections
    end

let initialize_conn_2 n s sin sout =
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
  let cs = { conntime = tm; realaddr = n; connmutex = Mutex.create(); sendqueue = Queue.create(); sendqueuenonempty = Condition.create(); handshakestep = 2; peertimeskew = 0; protvers = Version.protocolversion; useragent = ""; addrfrom = ""; locked = false; lastmsgtm = tm; pending = []; sentinv = []; rinv = []; invreq = []; first_header_height = fhh; first_full_height = ffh; last_height = lh } in
  queue_msg cs Version (Buffer.contents vm);
  let sgcs = (s,sin,sout,ref (Some(cs))) in
  let clth = Thread.create connlistener sgcs in
  let csth = Thread.create connsender sgcs in
  Mutex.lock netconnsmutex;
  netconns := (clth,csth,sgcs)::!netconns;
  Mutex.unlock netconnsmutex;
  (clth,csth,sgcs)

let initialize_conn n s =
  let sin = Unix.in_channel_of_descr s in
  let sout = Unix.out_channel_of_descr s in
  set_binary_mode_in sin true;
  set_binary_mode_out sout true;
  initialize_conn_2 n s sin sout

let tryconnectpeer n =
  if List.length !netconns >= !Config.maxconns then raise EnoughConnections;
  if Hashtbl.mem bannedpeers n then raise BannedPeer;
  try
    Some(List.find (fun (_,_,(_,_,_,gcs)) -> n = peeraddr !gcs) !netconns);
  with Not_found ->
    let (ip,port,v6) = extract_ip_and_port n in
    begin
      try
	match !Config.socks with
	| None ->
	    let s = connectpeer ip port in
	    Some (initialize_conn n s)
	| Some(4) ->
	    let (s,sin,sout) = connectpeer_socks4 !Config.socksport ip port in
	    Some (initialize_conn_2 n s sin sout)
	| Some(5) ->
	    raise (Failure "socks5 is not yet supported")
	| Some(z) ->
	    raise (Failure ("socks" ^ (string_of_int z) ^ " is not yet supported"))
      with
      | RequestRejected ->
	  Printf.fprintf !log "RequestRejected\n"; flush !log;
	  None
      | _ ->
	  None
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
			  (fun (_,_,(_,_,_,gcs)) -> peeraddr !gcs = n)
			  !netconns)
	      with Not_found -> ignore (tryconnectpeer n)
	      )
	    knownpeers
	end;
      if !netconns = [] then
	begin
	  List.iter
	    (fun n -> ignore (tryconnectpeer n))
	    (if !Config.testnet then testnetfallbacknodes else fallbacknodes)
	end;
      Unix.sleep 600;
    with
    | _ -> ()
  done

let netseeker () =
  loadknownpeers();
  netseekerth := Some(Thread.create netseeker_loop ())

let broadcast_requestdata mt h =
  let i = int_of_msgtype mt in
  let msb = Buffer.create 20 in
  seosbf (seo_hashval seosb h (msb,None));
  let ms = Buffer.contents msb in
  List.iter
    (fun (lth,sth,(fd,sin,sout,gcs)) ->
       match !gcs with
       | Some(cs) ->
         if not (List.mem (i,h) cs.invreq) then
           begin
             queue_msg cs mt ms;
             cs.invreq <- (i,h)::cs.invreq
           end
       | None -> ())
    !netconns

let broadcast_new_header h =
  List.iter
    (fun (lth,sth,(fd,sin,sout,gcs)) ->
       match !gcs with
       | Some(cs) ->
	   let s = Buffer.create 20 in
	   seosbf (seo_hashval seosb h (s,None));
	   ignore (queue_msg cs NewHeader (Buffer.contents s))
       | None -> ())
    !netconns

let broadcast_inv tosend =
  let invmsg = Buffer.create 10000 in
  let c = ref (seo_int32 seosb (Int32.of_int (List.length tosend)) (invmsg,None)) in
  List.iter
    (fun (i,blkh,h) ->
      c := seo_prod3 seo_int8 seo_int64 seo_hashval seosb (i,blkh,h) !c)
    tosend;
  let invmsgstr = Buffer.contents invmsg in
  List.iter
    (fun (lth,sth,(fd,sin,sout,gcs)) ->
      match !gcs with
      | Some(cs) -> ignore (queue_msg cs Inv invmsgstr)
      | None -> ())
    !netconns
