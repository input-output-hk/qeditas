(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Ser
open Hash
open Assets
open Signat
open Tx
open Ctre
open Block

(*** recent (provisional) data ***)
(*** recentledgerroots: associate ledger (ctree) roots with a block height and abbrev hashval ***)
(*** recentblockheaders: associate block header hash with block height and block header ***)
(*** recentblockdeltahs: associate block header hash with a blockdeltah (summarizing stxs by hashvals) ***)
(*** recentblockdeltas: associate block header hash with a blockdelta (with all stxs explicit) ***)
(*** recentstxs: associate hashes of txs/stxs with stxs (may or may not be in blocks) ***)
let recentledgerroots : (hashval, int64 * hashval) Hashtbl.t = Hashtbl.create 1024
let recentblockheaders : (hashval * (big_int * int64 * blockheader)) list ref = ref [] (*** ordered by cumulative stake ***)
let recentcommitments : (int64 * hashval) list ref = ref []
let recentblockdeltahs : (hashval, blockdeltah) Hashtbl.t = Hashtbl.create 1024
let recentblockdeltas : (hashval, blockdelta) Hashtbl.t = Hashtbl.create 1024
let recentstxs : (hashval, stx) Hashtbl.t = Hashtbl.create 65536

let waitingblock : (int64 * int64 * hashval * blockheader * blockdelta * big_int) option ref = ref None;;

let rec insertnewblockheader_real bhh cs mine blkh bh l =
  match l with
  | (bhh1,(cs1,blkh1,bh1))::r when lt_big_int cs1 cs || (mine && eq_big_int cs1 cs) -> (bhh,(cs,blkh,bh))::l (*** consider the ones this process has created preferable to others with the same cumulative stake ***)
  | x::r -> x::insertnewblockheader_real bhh cs mine blkh bh r
  | [] -> [(bhh,(cs,blkh,bh))]

let insertnewblockheader bhh cs mine blkh bh =
  recentblockheaders := insertnewblockheader_real bhh cs mine blkh bh !recentblockheaders;
  Printf.printf "After insertnewblockheader\n";
  List.iter
    (fun (bhh1,(cs1,blkh1,bh1)) ->
      Printf.printf "%Ld %s cs: %s timestamp %Ld\n" blkh1 (hashval_hexstring bhh1) (string_of_big_int cs1) (let (bhd1,_) = bh1 in bhd1.timestamp)
      )
    !recentblockheaders;
  flush stdout

exception RequestRejected
exception Hung
exception IllformedMsg

let sethungsignalhandler () =
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Hung));;
  
let accept_nohang s tm =
  try
    ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = tm });
    let (s2,a2) = Unix.accept s in
    try
      ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = 0.0 });
      Some(s2,a2)
    with Hung -> (** in case the alarm is signaled after the connection was accepted but before the function returned, catch Hung and continue **)
      ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = 0.0 });
      Some(s2,a2)
  with Hung -> None

let input_byte_nohang c tm =
  try
    ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = tm });
    let b = input_byte c in
    try
      ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = 0.0 });
      Some(b)
    with Hung -> (** in case the alarm is signaled after the connection was accepted but before the function returned, catch Hung and continue **)
      ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = 0.0 });
      Some(b)
  with Hung -> None

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
  Printf.printf "%d %d\n" z cd; flush stdout;
  if not (cd = 90) then raise RequestRejected;
  for i = 1 to 6 do
    ignore (input_byte sin)
  done;
  (s,sin,sout)

type msg =
  | Version of int32 * int64 * int64 * string * string * int64 * string * rframe * rframe * rframe * int64 * int64 * int64 * bool * (int64 * hashval) option
  | Verack
  | Addr of (int64 * string) list
  | Inv of (int * int64 * hashval) list (*** for blocks (headers, deltahs, deltas) and ctrees, include the corrsponding block height (int64) ***)
  | GetData of (int * hashval) list
  | MNotFound of (int * hashval) list
  | GetBlocks of int32 * int64 * hashval option
  | GetBlockdeltas of int32 * int64 * hashval option
  | GetBlockdeltahs of int32 * int64 * hashval option
  | GetHeaders of int32 * int64 * hashval option
  | MTx of int32 * stx (*** signed tx in principle, but in practice some or all signatures may be missing ***)
  | MBlock of int32 * block
  | Headers of (int64 * blockheader) list
  | MBlockdelta of int32 * hashval * blockdelta (*** the hashval is for the block header ***)
  | MBlockdeltah of int32 * hashval * blockdeltah (*** the hashval is for the block header; the blockdeltah only has the hashes of stxs in the block ***)
  | GetAddr
  | Mempool
  | Alert of string * signat
  | Ping
  | Pong
  | Reject of string * int * string * string
  | GetFramedCTree of int32 * int64 option * hashval * rframe
  | MCTree of int32 * ctree
  | Checkpoint of int64 * hashval
  | AntiCheckpoint of int64 * hashval

type pendingcallback = PendingCallback of (msg -> pendingcallback option)

type connstate = {
    mutable alive : bool;
    mutable lastmsgtm : float;
    mutable pending : (hashval * bool * float * float * pendingcallback option) list;
    mutable sentinv : (int * hashval) list;
    mutable rinv : (int * hashval) list;
    mutable invreq : (int * hashval) list;
    mutable rframe0 : rframe; (*** which parts of the ctree the node is keeping ***)
    mutable rframe1 : rframe; (*** what parts of the ctree are stored by a node one hop away ***)
    mutable rframe2 : rframe; (*** what parts of the ctree are stored by a node two hops away ***)
    mutable first_header_height : int64; (*** how much header history is stored at the node ***)
    mutable first_full_height : int64; (*** how much block/ctree history is stored at the node ***)
    mutable last_height : int64; (*** how up to date the node is ***)
  }

let conns = ref [];;

let seo_msg o m c =
  match m with
  | Version(vers,srvs,tm,addr_recv,addr_from,nonce,user_agent,fr0,fr1,fr2,first_header_height,first_full_height,latest_height,relay,lastchkpt) ->
      let c = o 8 0 c in
      let c = seo_int32 o vers c in
      let c = seo_int64 o srvs c in
      let c = seo_int64 o tm c in
      let c = seo_string o addr_recv c in
      let c = seo_string o addr_from c in
      let c = seo_int64 o nonce c in
      let c = seo_string o user_agent c in
      let c = seo_rframe o fr0 c in
      let c = seo_rframe o fr1 c in
      let c = seo_rframe o fr2 c in
      let c = seo_int64 o first_header_height c in
      let c = seo_int64 o first_full_height c in
      let c = seo_int64 o latest_height c in
      let c = seo_bool o relay c in
      let c = seo_option (seo_prod seo_int64 seo_hashval) o lastchkpt c in
      c
  | Verack -> o 8 1 c
  | Addr(addr_list) ->
      if List.length addr_list > 1000 then raise (Failure "Cannot send more than 1000 node addresses");
      let c = o 8 2 c in
      let c = seo_list (seo_prod seo_int64 seo_string) o addr_list c in
      c
  | Inv(invl) ->
      if List.length invl > 50000 then raise (Failure "Cannot send more than 50000 inventory items");
      let c = o 8 3 c in
      let c = seo_list (seo_prod3 seo_int8 seo_int64 seo_hashval) o invl c in
      c
  | GetData(invl) ->
      if List.length invl > 50000 then raise (Failure "Cannot send more than 50000 data requests");
      let c = o 8 4 c in
      let c = seo_list (seo_prod seo_int8 seo_hashval) o invl c in
      c
  | MNotFound(invl) ->
      if List.length invl > 50000 then raise (Failure "Cannot send more than 50000 'not found' replies");
      let c = o 8 5 c in
      let c = seo_list (seo_prod seo_int8 seo_hashval) o invl c in
      c
  | GetBlocks(vers,blkh,hash_stop) ->
      let c = o 8 6 c in
      let c = seo_int32 o vers c in
      let c = seo_int64 o blkh c in
      let c = seo_option seo_hashval o hash_stop c in
      c
  | GetBlockdeltas(vers,blkh,hash_stop) ->
      let c = o 8 7 c in
      let c = seo_int32 o vers c in
      let c = seo_int64 o blkh c in
      let c = seo_option seo_hashval o hash_stop c in
      c
  | GetBlockdeltahs(vers,blkh,hash_stop) ->
      let c = o 8 8 c in
      let c = seo_int32 o vers c in
      let c = seo_int64 o blkh c in
      let c = seo_option seo_hashval o hash_stop c in
      c
  | GetHeaders(vers,blkh,hash_stop) ->
      let c = o 8 9 c in
      let c = seo_int32 o vers c in
      let c = seo_int64 o blkh c in
      let c = seo_option seo_hashval o hash_stop c in
      c
  | MTx(vers,tau) ->
      let c = o 8 10 c in
      let c = seo_int32 o vers c in
      let c = seo_stx o tau c in
      c
  | MBlock(vers,b) ->
      let c = o 8 11 c in
      let c = seo_int32 o vers c in
      let c = seo_block o b c in
      c
  | Headers(bhl) ->
      if List.length bhl > 1000 then raise (Failure "Cannot send more than 1000 headers");
      let c = o 8 12 c in
      let c = seo_list (seo_prod seo_int64 seo_blockheader) o bhl c in
      c
  | MBlockdelta(vers,h,del) ->
      let c = o 8 13 c in
      let c = seo_int32 o vers c in
      let c = seo_hashval o h c in
      let c = seo_blockdelta o del c in
      c
  | MBlockdeltah(vers,h,del) ->
      let c = o 8 14 c in
      let c = seo_int32 o vers c in
      let c = seo_hashval o h c in
      let c = seo_blockdeltah o del c in
      c
  | GetAddr -> o 8 15 c
  | Mempool -> o 8 16 c
  | Alert(m,sg) ->
      let c = o 8 17 c in
      let c = seo_string o m c in
      let c = seo_signat o sg c in
      c
  | Ping -> o 8 18 c
  | Pong -> o 8 19 c
  | Reject(m,ccode,rsn,data) ->
      let c = o 8 20 c in
      let c = seo_string o m c in
      let c = seo_int8 o ccode c in
      let c = seo_string o rsn c in
      let c = seo_string o data c in
      c
  | GetFramedCTree(vers,blkh,cr,fr) ->
      let c = o 8 21 c in
      let c = seo_int32 o vers c in
      let c = seo_option seo_int64 o blkh c in
      let c = seo_hashval o cr c in
      let c = seo_rframe o fr c in
      c
  | MCTree(vers,ctr) ->
      let c = o 8 22 c in
      let c = seo_int32 o vers c in
      let c = seo_ctree o ctr c in
      c
  | Checkpoint(blkh,h) ->
      let c = o 8 23 c in
      let c = seo_int64 o blkh c in
      let c = seo_hashval o h c in
      c
  | AntiCheckpoint(blkh,h) ->
      let c = o 8 24 c in
      let c = seo_int64 o blkh c in
      let c = seo_hashval o h c in
      c

let sei_msg i c =
  let (by,c) = i 8 c in
  match by with
  | 0 ->
      let (vers,c) = sei_int32 i c in
      let (srvs,c) = sei_int64 i c in
      let (tm,c) = sei_int64 i c in
      let (addr_recv,c) = sei_string i c in
      let (addr_from,c) = sei_string i c in
      let (nonce,c) = sei_int64 i c in
      let (user_agent,c) = sei_string i c in
      let (fr0,c) = sei_rframe i c in
      let (fr1,c) = sei_rframe i c in
      let (fr2,c) = sei_rframe i c in
      let (first_header_height,c) = sei_int64 i c in
      let (first_full_height,c) = sei_int64 i c in
      let (latest_height,c) = sei_int64 i c in
      let (relay,c) = sei_bool i c in
      let (lastchkpt,c) = sei_option (sei_prod sei_int64 sei_hashval) i c in
      (Version(vers,srvs,tm,addr_recv,addr_from,nonce,user_agent,fr0,fr1,fr2,first_header_height,first_full_height,latest_height,relay,lastchkpt),c)
  | 1 ->
      (Verack,c)
  | 2 ->
      let (addr_list,c) = sei_list (sei_prod sei_int64 sei_string) i c in
      (Addr(addr_list),c)
  | 3 ->
      let (invl,c) = sei_list (sei_prod3 sei_int8 sei_int64 sei_hashval) i c in
      (Inv(invl),c)
  | 4 ->
      let (invl,c) = sei_list (sei_prod sei_int8 sei_hashval) i c in
      (GetData(invl),c)
  | 5 ->
      let (invl,c) = sei_list (sei_prod sei_int8 sei_hashval) i c in
      (MNotFound(invl),c)
  | 6 ->
      let (vers,c) = sei_int32 i c in
      let (blkh,c) = sei_int64 i c in
      let (hash_stop,c) = sei_option sei_hashval i c in
      (GetBlocks(vers,blkh,hash_stop),c)
  | 7 ->
      let (vers,c) = sei_int32 i c in
      let (blkh,c) = sei_int64 i c in
      let (hash_stop,c) = sei_option sei_hashval i c in
      (GetBlockdeltas(vers,blkh,hash_stop),c)
  | 8 ->
      let (vers,c) = sei_int32 i c in
      let (blkh,c) = sei_int64 i c in
      let (hash_stop,c) = sei_option sei_hashval i c in
      (GetBlockdeltahs(vers,blkh,hash_stop),c)
  | 9 ->
      let (vers,c) = sei_int32 i c in
      let (blkh,c) = sei_int64 i c in
      let (hash_stop,c) = sei_option sei_hashval i c in
      (GetHeaders(vers,blkh,hash_stop),c)
  | 10 ->
      let (vers,c) = sei_int32 i c in
      let (tau,c) = sei_stx i c in
      (MTx(vers,tau),c)
  | 11 ->
      let (vers,c) = sei_int32 i c in
      let (b,c) = sei_block i c in
      (MBlock(vers,b),c)
  | 12 ->
      let (bhl,c) = sei_list (sei_prod sei_int64 sei_blockheader) i c in
      (Headers(bhl),c)
  | 13 ->
      let (vers,c) = sei_int32 i c in
      let (h,c) = sei_hashval i c in
      let (del,c) = sei_blockdelta i c in
      (MBlockdelta(vers,h,del),c)
  | 14 ->
      let (vers,c) = sei_int32 i c in
      let (h,c) = sei_hashval i c in
      let (del,c) = sei_blockdeltah i c in
      (MBlockdeltah(vers,h,del),c)
  | 15 -> (GetAddr,c)
  | 16 -> (Mempool,c)
  | 17 ->
      let (m,c) = sei_string i c in
      let (sg,c) = sei_signat i c in
      (Alert(m,sg),c)
  | 18 -> (Ping,c)
  | 19 -> (Pong,c)
  | 20 ->
      let (m,c) = sei_string i c in
      let (ccode,c) = sei_int8 i c in
      let (rsn,c) = sei_string i c in
      let (data,c) = sei_string i c in
      (Reject(m,ccode,rsn,data),c)
  | 21 ->
      let (vers,c) = sei_int32 i c in
      let (blkh,c) = sei_option sei_int64 i c in
      let (cr,c) = sei_hashval i c in
      let (fr,c) = sei_rframe i c in
      (GetFramedCTree(vers,blkh,cr,fr),c)
  | 22 ->
      let (vers,c) = sei_int32 i c in
      let (ctr,c) = sei_ctree i c in
      (MCTree(vers,ctr),c)
  | 23 ->
      let (blkh,c) = sei_int64 i c in
      let (h,c) = sei_hashval i c in
      (Checkpoint(blkh,h),c)
  | 24 ->
      let (blkh,c) = sei_int64 i c in
      let (h,c) = sei_hashval i c in
      (AntiCheckpoint(blkh,h),c)
  | _ ->
      raise (Failure "Unrecognized Message Type")

let send_msg_real c replyto m =
  let magic = if !Config.testnet then 0x51656454l else 0x5165644dl in
  let sb = Buffer.create 1000 in
  seosbf (seo_msg seosb m (sb,None));
  let ms = Buffer.contents sb in
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
  output_byte c (Char.code ms.[0]);
  seocf (seo_int32 seoc (Int32.of_int msl) (c,None));
  let mh = hash160 ms in
  seocf (seo_hashval seoc mh (c,None));
  for j = 0 to msl-1 do
    output_byte c (Char.code ms.[j])
  done;
  flush c;
  mh

let send_msg c m = send_msg_real c None m
let send_reply c h m = send_msg_real c (Some(h)) m

let broadcast_inv invl =
  let invl2 = List.map (fun (k,_,h) -> (k,h)) invl in
  List.iter
    (fun (s,sin,sout,peeraddr,cs) ->
      try
	if cs.alive then
	  begin
	    ignore (send_msg sout (Inv(invl)));
	    cs.sentinv <- invl2 @ cs.sentinv
	  end
      with _ -> ())
    !conns

let send_initial_inv sout cs =
  let tosend = ref [] in
  let cnt = ref 0 in
  List.iter (fun (bhh,(cumulstk,blkh,bh)) ->
    incr cnt;
    if !cnt < 50000 then
      begin
	tosend := (1,blkh,bhh)::!tosend;
	if Hashtbl.mem recentblockdeltahs bhh then (incr cnt; if !cnt < 50000 then tosend := (2,blkh,bhh)::!tosend);
	if Hashtbl.mem recentblockdeltas bhh then (incr cnt; if !cnt < 50000 then tosend := (3,blkh,bhh)::!tosend);
      end)
    !recentblockheaders;
  Hashtbl.iter (fun txh _ -> incr cnt; if !cnt < 50000 then tosend := (4,0L,txh)::!tosend) recentstxs;
  send_msg sout (Inv(!tosend));
  cs.sentinv <- List.map (fun (k,_,h) -> (k,h)) !tosend

(***
 Throw IllformedMsg if something's wrong with the format or if it reads the first byte but times out before reading the full message.
 If IllformedMsg is thrown, the connection should be severed.
 ***)
let rec_msg_nohang c tm tm2 =
  let (mag0,mag1,mag2,mag3) = if !Config.testnet then (0x51,0x65,0x64,0x54) else (0x51,0x65,0x64,0x4d) in
  let by0 = input_byte_nohang c tm in
  match by0 with
  | None -> None
  | Some(by0) ->
      begin
	if not (by0 = mag0) then raise IllformedMsg;
	try
	  ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = tm2 });
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
	  let comm = input_byte c in
	  let (msl,_) = sei_int32 seic (c,None) in
	  if msl > 67108863l then raise IllformedMsg;
	  let msl = Int32.to_int msl in
	  let (mh,_) = sei_hashval seic (c,None) in
	  let sb = Buffer.create msl in
	  let by0 = input_byte c in
	  if not (by0 = comm) then raise IllformedMsg;
	  Buffer.add_char sb (Char.chr by0);
	  for j = 1 to msl-1 do
	    let by = input_byte c in
	    Buffer.add_char sb (Char.chr by)
	  done;
	  ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = 0.0 }); (*** finished reading the message, so no need to time out now ***)
	  let ms = Buffer.contents sb in
	  if not (mh = hash160 ms) then raise IllformedMsg;
	  let (m,_) = sei_msg seis (ms,msl,None,0,0) in
	  Some(replyto,mh,m)
	with
	| _ -> (*** consider it an IllformedMsg no matter what the exception raised was ***)
	    ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = 0.0 });
	    raise IllformedMsg
      end

let known_blockheader_p blkh h =
  List.mem_assoc h !recentblockheaders (*** should also check if it's in a file ***)

let known_blockdeltah_p blkh h =
  Hashtbl.mem recentblockdeltahs h (*** should also check if it's in a file ***)

let known_blockdelta_p blkh h =
  Hashtbl.mem recentblockdeltas h (*** should also check if it's in a file ***)

let known_stx_p h =
  Hashtbl.mem recentstxs h (*** should also check if it's in a file ***)

let rec update_pending pendl k m =
  match pendl with
  | [] -> []
  | (h,p,tm1,tm2,None)::pendr when not (h = k) ->
      (h,p,tm1,tm2,None)::update_pending pendr k m
  | (h,p,tm1,tm2,None)::pendr ->
      pendr
  | (h,p,tm1,tm2,Some(PendingCallback(f)))::pendr ->
      match f m with
      | None -> pendr
      | g -> (h,p,tm1,Unix.time(),g)::pendr
	  
let handle_msg sin sout cs replyto mh m =
  match (replyto,m) with
  | (None,Ping) ->
      Printf.printf "Handling Ping. Sending Pong.\n"; flush stdout;
      ignore (send_reply sout mh Pong);
      Printf.printf "Sent Pong.\n"; flush stdout
  | (Some(pingh),Pong) ->
      Printf.printf "Handling Pong.\n"; flush stdout;
      cs.pending <- update_pending cs.pending pingh m
  | (Some(qh),Reject(msgcom,by,rsn,data)) ->
      Printf.printf "Message %s %s rejected: %d %s\n" (hashval_hexstring mh) msgcom by rsn;
      flush stdout;
      cs.pending <- update_pending cs.pending qh m
  | (None,Inv(invl)) ->
      let toget = ref [] in
      List.iter
	(fun (k,blkh,h) ->
	  cs.rinv <- (k,h)::cs.rinv;
	  match k with
	  | 1 -> (*** block header ***)
	      if not (known_blockheader_p blkh h) then toget := (k,h)::!toget
	  | 2 -> (*** blockdeltah ***)
	      if not (known_blockdeltah_p blkh h) then toget := (k,h)::!toget
	  | 3 -> (*** blockdelta ***)
	      if not (known_blockdelta_p blkh h) then toget := (k,h)::!toget
	  | 4 -> (*** stx ***)
	      if not (known_stx_p h) then toget := (k,h)::!toget
	  | _ -> () (*** ignore everything else for now ***)
	)
	invl;
      if not (!toget = []) then
	let mh = send_msg sout (GetData(!toget)) in
	cs.invreq <- !toget @ cs.invreq
  | (None,GetData(invl)) ->
      let headerl = ref [] in
      List.iter
	(fun (k,h) ->
	  if k = 1 then
	    try
	      let (_,blkh,bh) = List.assoc h !recentblockheaders in headerl := (blkh,bh)::!headerl
	    with Not_found -> (*** should look for it in a file in this case ***)
	      ())
	invl;
      ignore (send_msg sout (Headers(List.rev !headerl)));
      List.iter
	(fun (k,h) ->
	  match k with
	  | 1 -> () (*** block headers sent above ***)
	  | 2 -> (*** blockdeltah ***)
	      begin
		try
		  let bdh = Hashtbl.find recentblockdeltahs h in
		  ignore (send_msg sout (MBlockdeltah(1l,h,bdh)))
		with Not_found -> () (*** should look for it in a file in this case ***)
	      end
	  | 3 -> (*** blockdelta ***)
	      begin
		try
		  let bd = Hashtbl.find recentblockdeltas h in
		  ignore (send_msg sout (MBlockdelta(1l,h,bd)))
		with Not_found -> () (*** should look for it in a file in this case ***)
	      end
	  | 4 -> (*** stx ***)
	      begin
		try
		  let stx = Hashtbl.find recentstxs h in
		  ignore (send_msg sout (MTx(1l,stx)))
		with Not_found -> () (*** should look for it in a file in this case ***)
	      end
	  | _ -> () (*** ignore everything else for now ***)
	  )
	invl
  | (None,Headers(bhl)) ->
      let tm = Int64.of_float (Unix.time()) in
      List.iter
	(fun (blkh,(bhd,bhs)) ->
	  let bhdh = hash_blockheaderdata bhd in
	  if List.mem (1,bhdh) cs.invreq then (*** only accept if it seems to have been requested ***)
	    begin
	      cs.invreq <- List.filter (fun (k,h) -> not (k = 1 && h = bhdh)) cs.invreq;
	      if bhd.timestamp <= Int64.add tm 60L then (*** do not accept blockheaders from too far the future ***)
		match 
		  match bhd.prevblockhash with
		  | None ->
		      Printf.printf "genesis\n";
		      if valid_blockheaderchain blkh ((bhd,bhs),[]) (*** first block, special conditions ***)
		      then Some(zero_big_int)
		      else None
		  | Some(pbhh) ->
		      begin
			try
			  let (cs,_,pbh) = List.assoc pbhh !recentblockheaders in
			  if blockheader_succ pbh (bhd,bhs) then
			    Some(cs)
			  else
			    None
			with Not_found -> None (*** reject orphan headers ***)
		      end
		with
		| Some(cumulstk) -> (*** header is accepted, put it on the list with the new cumulative stake ***)
		    Printf.printf "Got header with cumul stake: %s\n" (string_of_big_int cumulstk); flush stdout;
		    let (_,_,tar) = bhd.tinfo in
		    let bhdh = hash_blockheaderdata bhd in
		    if not (known_blockheader_p blkh bhdh) then (*** make sure it's new ***)
		      begin
			insertnewblockheader (hash_blockheaderdata bhd) (cumul_stake cumulstk tar bhd.deltatime) false blkh (bhd,bhs);
			begin (*** If there is some block we are waiting to publish, see if it has more cumulative stake that this one. If not, forget it. ***)
			  match !waitingblock with
			  | Some(_,_,_,_,_,mycumulstk) when lt_big_int mycumulstk cumulstk ->
			      Printf.printf "A better block was found. Not publishing mine.\n"; flush stdout;
			      waitingblock := None
			  | _ -> ()
			end;
			if List.mem (2,bhdh) cs.rinv then (*** request the corresponding blockdeltah if possible ***)
			  begin
			    ignore (send_msg sout (GetData([(2,bhdh)])));
			    cs.invreq <- (2,bhdh)::cs.invreq
			  end
			else if List.mem (3,bhdh) cs.rinv then (*** otherwise request the corresponding blockdelta if possible ***)
			  begin
			    ignore (send_msg sout (GetData([(3,bhdh)])));
			    cs.invreq <- (3,bhdh)::cs.invreq
			  end
		      end
		| None -> (*** header is rejected, ignore it for now, maybe should ignore it forever? ***)
		    Printf.printf "header rejected\n";
		    ()
	    end)
	bhl
  | (None,MBlockdeltah(vers,h,bdh)) ->
      Printf.printf "Handling MBlockdeltah.\n"; flush stdout;
      if List.mem (2,h) cs.invreq then (*** only accept if it seems to have been requested ***)
	begin
	  cs.invreq <- List.filter (fun (k,h2) -> not (k = 2 && h2 = h)) cs.invreq;
	  Hashtbl.add recentblockdeltahs h bdh
	end
  | (None,MBlockdelta(vers,h,bd)) ->
      Printf.printf "Handling MBlockdeltah.\n"; flush stdout;
      if List.mem (3,h) cs.invreq then (*** only accept if it seems to have been requested ***)
	begin
	  cs.invreq <- List.filter (fun (k,h2) -> not (k = 3 && h2 = h)) cs.invreq;
	  Hashtbl.add recentblockdeltas h bd
	end
  | (None,MTx(vers,(tx,txsig))) ->
      let h = hashtx tx in
      if List.mem (4,h) cs.invreq then (*** only accept if it seems to have been requested ***)
	begin
	  cs.invreq <- List.filter (fun (k,h2) -> not (k = 4 && h2 = h)) cs.invreq;
	  Hashtbl.add recentstxs h (tx,txsig)
	end
  | (None,GetFramedCTree(vers,blkho,cr,fr)) ->
      Printf.printf "Handling GetFramedCTree.\n"; flush stdout;
      List.iter
        (fun (_,ca) ->
    	  let c = CAbbrev(cr,ca) in
	  try
	    let ctosend = rframe_filter_ctree fr c in
	    ignore (send_reply sout mh (MCTree(0l,ctosend)))
	  with
	  | _ -> () (*** try a different abbrev corresponding to the root ***)
	)
	(lookup_all_ctree_root_abbrevs cr);
      ignore (send_reply sout mh (Reject("GetFramedCTree",1,"could not build framed ctree","")))
  | (Some(qh),MCTree(vers,ctr)) ->
      cs.pending <- update_pending cs.pending qh m
  | _ ->
      Printf.printf "Ignoring msg, probably because the code to handle the msg is unwritten.\n"; flush stdout

let try_requests rql =
  List.iter
    (fun (s,sin,sout,addrfrom,cs) ->
      let rql1 = List.filter (fun (k,h) -> List.mem (k,h) cs.rinv && not (List.mem (k,h) cs.invreq)) rql in
      if not (rql1 = []) then
	begin
	  ignore (send_msg sout (GetData(rql1)));
	  cs.invreq <- rql1 @ cs.invreq
	end
    )
    !conns
