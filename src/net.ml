(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser
open Hash
open Assets
open Signat
open Tx
open Ctre
open Block

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
  | Version of int32 * int64 * int64 * string * string * int64 * string * rframe * rframe * rframe * int64 * int64 * bool * (int64 * hashval) option
  | Verack
  | Addr of (int64 * string) list
  | Inv of (int * hashval) list
  | GetData of (int * hashval) list
  | MNotFound of (int * hashval) list
  | GetBlocks of int32 * int64 * hashval option
  | GetBlockdeltas of int32 * int64 * hashval option
  | GetBlockdeltahs of int32 * int64 * hashval option
  | GetHeaders of int32 * int64 * hashval option
  | MTx of int32 * stx (*** signed tx in principle, but in practice some or all signatures may be missing ***)
  | MBlock of int32 * block
  | Headers of blockheader list
  | MBlockdelta of int32 * hashval * blockdelta (*** the hashval is for the block header ***)
  | MBlockdeltah of int32 * hashval * blockdeltah (*** the hashval is for the block header; the blockdeltah only has the hashes of stxs in the block ***)
  | GetAddr
  | Mempool
  | Alert of string * signat
  | Ping
  | Pong
  | Reject of string * int * string * string
  | GetFramedCTree of int32 * int64 option * hashval * rframe
  | Checkpoint of int64 * hashval
  | AntiCheckpoint of int64 * hashval

type pendingcallback = PendingCallback of (msg -> pendingcallback option)

type connstate = {
    alive : bool;
    lastmsgtime : float;
    pending : (hashval * float * float * pendingcallback) list;
    rframe0 : rframe; (*** which parts of the ctree the node is keeping ***)
    rframe1 : rframe; (*** what parts of the ctree are stored by a node one hop away ***)
    rframe2 : rframe; (*** what parts of the ctree are stored by a node two hops away ***)
    first_height : int64; (*** how much history is stored at the node ***)
    last_height : int64; (*** how up to date the node is ***)
  }

let seo_msg o m c =
  match m with
  | Version(vers,srvs,tm,addr_recv,addr_from,nonce,user_agent,fr0,fr1,fr2,first_height,latest_height,relay,lastchkpt) ->
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
      let c = seo_int64 o first_height c in
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
      let c = seo_list (seo_prod seo_int8 seo_hashval) o invl c in
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
      let c = seo_list seo_blockheader o bhl c in
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
  | Checkpoint(blkh,h) ->
      let c = o 8 22 c in
      let c = seo_int64 o blkh c in
      let c = seo_hashval o h c in
      c
  | AntiCheckpoint(blkh,h) ->
      let c = o 8 23 c in
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
      let (first_height,c) = sei_int64 i c in
      let (latest_height,c) = sei_int64 i c in
      let (relay,c) = sei_bool i c in
      let (lastchkpt,c) = sei_option (sei_prod sei_int64 sei_hashval) i c in
      (Version(vers,srvs,tm,addr_recv,addr_from,nonce,user_agent,fr0,fr1,fr2,first_height,latest_height,relay,lastchkpt),c)
  | 1 ->
      (Verack,c)
  | 2 ->
      let (addr_list,c) = sei_list (sei_prod sei_int64 sei_string) i c in
      (Addr(addr_list),c)
  | 3 ->
      let (invl,c) = sei_list (sei_prod sei_int8 sei_hashval) i c in
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
      let (bhl,c) = sei_list sei_blockheader i c in
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
      let (blkh,c) = sei_int64 i c in
      let (h,c) = sei_hashval i c in
      (Checkpoint(blkh,h),c)
  | 23 ->
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
  done

let send_msg c m = send_msg_real c None m
let send_reply c h m = send_msg_real c (Some(h)) m

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

let handle_msg sin sout cst replyto mh m =
  match m with
  | Ping ->
      Printf.printf "Handling Ping. Sending Pong.\n"; flush stdout;
      send_reply sout mh Pong;
      Printf.printf "Sent Pong.\n"; flush stdout
  | Pong ->
      Printf.printf "Handling Pong.\n"; flush stdout;
      

  | _ ->
      Printf.printf "Ignoring msg since code to handle msg is unwritten.\n"; flush stdout
