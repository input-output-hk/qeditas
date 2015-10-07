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
    extract_ipv6_and_port ipp 1 l
  else
    extract_ipv4_and_port ipp 0 l

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
  | Version of int32 * int64 * int64 * string * string * int64 * string * int64 * bool
  | Verack
  | Addr of int * (int64 * string) list
  | Inv of int * (int * hashval) list
  | GetData of int * (int * hashval) list
  | MNotFound of int * (int * hashval) list
  | GetBlocks of int32 * int * hashval list * hashval option
  | GetHeaders of int32 * int * hashval list * hashval option
  | MTx of int32 * stx (*** signed tx in principle, but in practice some or all signatures may be missing ***)
  | MBlock of int32 * hashval * blockdeltah (*** the hashval is for the block header and blockdeltah only has the hashes of stxs in the block; the header and txs themselves can/should/must be requested separately ***)
  | Headers of int * blockheader list
  | GetAddr
  | Mempool
  | Alert of string * signat
  | Ping
  | Pong
  | Reject of string * int * string * string
  | MCTree of int32 * ctree
  | MNehList of int32 * nehlist
  | MHList of int32 * hlist
  | GetFramedCTree of int32 * hashval * frame

let send_string c x =
  let l = String.length x in
  let c2 = seo_varint seoc (Int64.of_int l) (c,None) in
  seocf c2;
  for i = 0 to l-1 do
    output_byte c (Char.code x.[i])
  done

let rec_string c =
  let (l64,_) = sei_varint seic (c,None) in
  let l = Int64.to_int l64 in
  let x = Buffer.create l in
  for i = 0 to l-1 do
    let b = input_byte c in
    Buffer.add_char x (Char.chr b)
  done;
  Buffer.contents x

let send_msg c m =
  match m with
  | Version(vers,srvs,tm,addr_recv,addr_from,nonce,user_agent,start_height,relay) ->
      output_byte c 0;
      let c2 = (c,None) in
      let c2 = seo_int32 seoc vers c2 in
      let c2 = seo_int64 seoc srvs c2 in
      let c2 = seo_int64 seoc tm c2 in
      let c2 = seo_int64 seoc nonce c2 in
      let c2 = seo_int64 seoc start_height c2 in
      let c2 = seo_bool seoc relay c2 in
      seocf c2;
      send_string c addr_recv;
      send_string c addr_from;
      send_string c user_agent;
      flush c
  | Verack ->
      output_byte c 1;
      flush c
  | Addr(cnt,addr_list) ->
      if cnt > 1000 then raise (Failure "Cannot send more than 1000 node addresses");
      if not (List.length addr_list = cnt) then raise (Failure "List does not match declared length");
      output_byte c 2;
      seocf (seo_varint seoc (Int64.of_int cnt) (c,None));
      List.iter
	(fun (tm,a) ->
	  seocf (seo_int64 seoc tm (c,None));
	  send_string c a)
	addr_list;
      flush c
  | Inv(cnt,invl) ->
      if cnt > 50000 then raise (Failure "Cannot send more than 50000 inventory items");
      if not (List.length invl = cnt) then raise (Failure "List does not match declared length");
      output_byte c 3;
      seocf (seo_varint seoc (Int64.of_int cnt) (c,None));
      List.iter
	(fun (tp,h) ->
	  output_byte c tp;
	  seocf (seo_hashval seoc h (c,None)))
	invl;
      flush c
  | GetData(cnt,invl) ->
      if cnt > 50000 then raise (Failure "Cannot send more than 50000 data requests");
      if not (List.length invl = cnt) then raise (Failure "List does not match declared length");
      output_byte c 4;
      seocf (seo_varint seoc (Int64.of_int cnt) (c,None));
      List.iter
	(fun (tp,h) ->
	  output_byte c tp;
	  seocf (seo_hashval seoc h (c,None)))
	invl;
      flush c
  | MNotFound(cnt,invl) ->
      if cnt > 50000 then raise (Failure "Cannot send more than 50000 'not found' replies");
      if not (List.length invl = cnt) then raise (Failure "List does not match declared length");
      output_byte c 5;
      seocf (seo_varint seoc (Int64.of_int cnt) (c,None));
      List.iter
	(fun (tp,h) ->
	  output_byte c tp;
	  seocf (seo_hashval seoc h (c,None)))
	invl;
      flush c
  | GetBlocks(vers,hash_count,blklocl,hash_stop) ->
      if not (List.length blklocl = hash_count) then raise (Failure "List does not match declared length");
      if hash_count > 50000 then raise (Failure "Cannot send more than 50000 of block locator hashes");
      output_byte c 6;
      seocf (seo_int32 seoc vers (c,None));
      seocf (seo_varint seoc (Int64.of_int hash_count) (c,None));
      List.iter
	(fun h ->
	  seocf (seo_hashval seoc h (c,None)))
	blklocl;
      seocf (seo_option seo_hashval seoc hash_stop (c,None));
      flush c
  | GetHeaders(vers,hash_count,blklocl,hash_stop) ->
      if not (List.length blklocl = hash_count) then raise (Failure "List does not match declared length");
      if hash_count > 50000 then raise (Failure "Cannot send more than 50000 of block locator hashes");
      output_byte c 7;
      seocf (seo_int32 seoc vers (c,None));
      seocf (seo_varint seoc (Int64.of_int hash_count) (c,None));
      List.iter
	(fun h ->
	  seocf (seo_hashval seoc h (c,None)))
	blklocl;
      seocf (seo_option seo_hashval seoc hash_stop (c,None));
      flush c
  | MTx(vers,tau) ->
      output_byte c 8;
      seocf (seo_int32 seoc vers (c,None));
      seocf (seo_stx seoc tau (c,None));
      flush c
  | MBlock(vers,h,del) ->
      output_byte c 9;
      seocf (seo_int32 seoc vers (c,None));
      seocf (seo_hashval seoc h (c,None));
      seocf (seo_blockdeltah seoc del (c,None));
      flush c
  | Headers(cnt,bhl) ->
      if cnt > 1000 then raise (Failure "Cannot send more than 1000 headers");
      if not (List.length bhl = cnt) then raise (Failure "List does not match declared length");
      output_byte c 10;
      seocf (seo_varint seoc (Int64.of_int cnt) (c,None));
      List.iter
	(fun bh ->
	  seocf (seo_blockheader seoc bh (c,None)))
	bhl;
      flush c
  | GetAddr ->
      output_byte c 11;
      flush c
  | Mempool ->
      output_byte c 12;
      flush c
  | Alert(msg,sg) ->
      output_byte c 13;
      send_string c msg;
      seocf (seo_signat seoc sg (c,None));
      flush c
  | Ping ->
      output_byte c 14;
      flush c
  | Pong ->
      output_byte c 15;
      flush c
  | Reject(msg,ccode,rsn,data) ->
      output_byte c 16;
      send_string c msg;
      output_byte c ccode;
      send_string c rsn;
      send_string c data;
      flush c
  | MCTree(vers,ctr) ->
      output_byte c 17;
      seocf (seo_int32 seoc vers (c,None));
      seocf (seo_ctree seoc ctr (c,None));
      flush c
  | MNehList(vers,hl) ->
      output_byte c 18;
      seocf (seo_int32 seoc vers (c,None));
      seocf (seo_nehlist seoc hl (c,None));
      flush c
  | MHList(vers,hl) ->
      output_byte c 19;
      seocf (seo_int32 seoc vers (c,None));
      seocf (seo_hlist seoc hl (c,None));
      flush c
  | GetFramedCTree(vers,cr,fr) ->
      output_byte c 20;
      seocf (seo_int32 seoc vers (c,None));
      seocf (seo_hashval seoc cr (c,None));
      seocf (seo_frame seoc fr (c,None));
      flush c

let rec_msg c =
  let by = input_byte c in
  match by with
  | 0 ->
      let (vers,c2) = sei_int32 seic (c,None) in
      let (srvs,c2) = sei_int64 seic c2 in
      let (tm,c2) = sei_int64 seic c2 in
      let (nonce,c2) = sei_int64 seic c2 in
      let (start_height,c2) = sei_int64 seic c2 in
      let (relay,_) = sei_bool seic c2 in
      let addr_recv = rec_string c in
      let addr_from = rec_string c in
      let user_agent = rec_string c in
      Version(vers,srvs,tm,addr_recv,addr_from,nonce,user_agent,start_height,relay)
  | 1 ->
      Verack
  | 2 ->
      let (cnt,_) = sei_varint seic (c,None) in
      let cnt = Int64.to_int cnt in
      if cnt > 1000 then raise (Failure "Cannot receive more than 1000 node addresses");
      let aa = Array.make cnt (0L,"") in
      for i = 0 to cnt-1 do
	let (tm,_) = sei_int64 seic (c,None) in
	let a = rec_string c in
	aa.(i) <- (tm,a)
      done;
      Addr(cnt,Array.to_list aa)
  | 3 ->
      let (cnt,_) = sei_varint seic (c,None) in
      let cnt = Int64.to_int cnt in
      if cnt > 50000 then raise (Failure "Cannot receive more than 50000 inventory items");
      let aa = Array.make cnt (0,(0l,0l,0l,0l,0l)) in
      for i = 0 to cnt-1 do
	let tp = input_byte c in
	let (h,_) = sei_hashval seic (c,None) in
	aa.(i) <- (tp,h)
      done;
      Inv(cnt,Array.to_list aa)
  | 4 ->
      let (cnt,_) = sei_varint seic (c,None) in
      let cnt = Int64.to_int cnt in
      if cnt > 50000 then raise (Failure "Cannot receive more than 50000 data requests");
      let aa = Array.make cnt (0,(0l,0l,0l,0l,0l)) in
      for i = 0 to cnt-1 do
	let tp = input_byte c in
	let (h,_) = sei_hashval seic (c,None) in
	aa.(i) <- (tp,h)
      done;
      GetData(cnt,Array.to_list aa)
  | 5 ->
      let (cnt,_) = sei_varint seic (c,None) in
      let cnt = Int64.to_int cnt in
      if cnt > 50000 then raise (Failure "Cannot receive more than 50000 'not found' replies");
      let aa = Array.make cnt (0,(0l,0l,0l,0l,0l)) in
      for i = 0 to cnt-1 do
	let tp = input_byte c in
	let (h,_) = sei_hashval seic (c,None) in
	aa.(i) <- (tp,h)
      done;
      MNotFound(cnt,Array.to_list aa)
  | 6 ->
      let (vers,_) = sei_int32 seic (c,None) in
      let (hash_count,_) = sei_varint seic (c,None) in
      let hash_count = Int64.to_int hash_count in
      if hash_count > 50000 then raise (Failure "Cannot receive more than 50000 block locator hashes");
      let aa = Array.make hash_count (0l,0l,0l,0l,0l) in
      for i = 0 to hash_count-1 do
	let (h,_) = sei_hashval seic (c,None) in
	aa.(i) <- h
      done;
      let (hash_stop,_) = sei_option sei_hashval seic (c,None) in
      GetBlocks(vers,hash_count,Array.to_list aa,hash_stop)
  | 7 ->
      let (vers,_) = sei_int32 seic (c,None) in
      let (hash_count,_) = sei_varint seic (c,None) in
      let hash_count = Int64.to_int hash_count in
      if hash_count > 50000 then raise (Failure "Cannot receive more than 50000 block locator hashes");
      let aa = Array.make hash_count (0l,0l,0l,0l,0l) in
      for i = 0 to hash_count-1 do
	let (h,_) = sei_hashval seic (c,None) in
	aa.(i) <- h
      done;
      let (hash_stop,_) = sei_option sei_hashval seic (c,None) in
      GetHeaders(vers,hash_count,Array.to_list aa,hash_stop)
  | 8 ->
      let (vers,_) = sei_int32 seic (c,None) in
      let (tau,_) = sei_stx seic (c,None) in
      MTx(vers,tau)
  | 9 ->
      let (vers,_) = sei_int32 seic (c,None) in
      let (h,_) = sei_hashval seic (c,None) in
      let (del,_) = sei_blockdeltah seic (c,None) in
      MBlock(vers,h,del)
  | 10 ->
      let (cnt,_) = sei_varint seic (c,None) in
      let cnt = Int64.to_int cnt in
      if cnt > 1000 then raise (Failure "Cannot receive more than 1000 headers");
      let aa = Array.make cnt fake_blockheader in
      for i = 0 to cnt-1 do
	let (bh,_) = sei_blockheader seic (c,None) in
	aa.(i) <- bh
      done;
      Headers(cnt,Array.to_list aa)
  | 11 ->
      GetAddr
  | 12 ->
      Mempool
  | 13 ->
      let msg = rec_string c in
      let (sg,_) = sei_signat seic (c,None) in
      Alert(msg,sg)
  | 14 ->
      Ping
  | 15 ->
      Pong
  | 16 ->
      let msg = rec_string c in
      let ccode = input_byte c in
      let rsn = rec_string c in
      let data = rec_string c in
      Reject(msg,ccode,rsn,data)
  | 17 ->
      let (vers,_) = sei_int32 seic (c,None) in
      let (ctr,_) = sei_ctree seic (c,None) in
      MCTree(vers,ctr)
  | 18 ->
      let (vers,_) = sei_int32 seic (c,None) in
      let (hl,_) = sei_nehlist seic (c,None) in
      MNehList(vers,hl)
  | 19 ->
      let (vers,_) = sei_int32 seic (c,None) in
      let (hl,_) = sei_hlist seic (c,None) in
      MHList(vers,hl)
  | 20 ->
      let (vers,_) = sei_int32 seic (c,None) in
      let (cr,_) = sei_hashval seic (c,None) in
      let (fr,_) = sei_frame seic (c,None) in
      GetFramedCTree(vers,cr,fr)
  | _ ->
      raise (Failure "Unrecognized Message Type")
