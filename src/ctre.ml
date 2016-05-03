(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Ser
open Hashaux
open Hash
open Mathdata
open Assets
open Cryptocurr
open Tx
open Config
open Db

let datadir () = if !testnet then (Filename.concat !datadir "testnet") else !datadir

let intention_minage = 144L

let sqr512 x = let y = big_int_of_int64 (Int64.add 1L (Int64.shift_right x 9)) in mult_big_int y y

let maximum_age = 16384L
let maximum_age_sqr = sqr512 maximum_age
let reward_maturation = 512L (*** rewards become stakable after 512 blocks ***)
let unlocked_maturation = 512L
let locked_maturation = 8L
let close_to_unlocked = 32L

(*** make reward locktime start at a very big number of 16384
  (so that initial rewards must be locked for at least 16384 blocks, about 4 months)
  but over time reduces to being locked for 128 blocks (about a day).
  It reduces by half each roughly 4 months until it reaches 128 after roughly 2 years.
  For block heights < 16384, the reward locktime is 16384.
  For block heights in [16384,32767], the reward locktime is 8192.
  For block heights in [32768,49151], the reward locktime is 4096.
  For block heights in [49152,65535], the reward locktime is 2048.
  For block heights in [65536,81919], the reward locktime is 1024.
  For block heights in [81920,98303], the reward locktime is 512.
  For block heights in [98304,114687], the reward locktime is 256.
  For block heights >= 114688, the reward locktime is 128
 ***)
let reward_locktime blkh =
  let a = Int64.shift_right blkh 14 in
  if a >= 7L then
    128L
  else
    let b = Int64.to_int a in
    Int64.shift_right 16384L b

let coinage blkh bday obl v =
  if bday = 0L then (*** coins in the initial distribution start out at maximum age ***)
    mult_big_int maximum_age_sqr (big_int_of_int64 v)
  else
    match obl with
    | None -> (*** unlocked ***)
	let mday = Int64.add bday unlocked_maturation in
	if mday >= blkh then (*** only start aging after it is mature ***)
	  zero_big_int
	else
	  let a = Int64.sub blkh mday in (*** how many blocks since the output became mature ***)
	  let a2 = if a < maximum_age then a else maximum_age in (*** up to maximum_age ***)
	  mult_big_int (sqr512 a2) (big_int_of_int64 v) (*** multiply the currency units by (a2/512)^2 ***)
    | Some(_,n,r) when r -> (*** in this case it's locked until block height n and is a reward ***)
	let mday = Int64.add bday reward_maturation in
	if mday >= blkh || Int64.add blkh close_to_unlocked >= n then (*** only start aging after it is mature and until it is close to unlocked ***)
	  zero_big_int
	else
	  let a = Int64.sub blkh mday in (*** how many blocks since the output became mature ***)
	  let a2 = if a < maximum_age then a else maximum_age in (*** up to maximum_age ***)
	  mult_big_int (sqr512 a2) (big_int_of_int64 v) (*** multiply the currency units by (a2/512)^2 ***)
    | Some(_,n,_) -> (*** in this case it's locked until block height n and is not a reward ***)
	let mday = Int64.add bday locked_maturation in
	if mday >= blkh || Int64.add blkh close_to_unlocked >= n then (*** only start aging after it is mature and until it is close to unlocked ***)
	  zero_big_int
	else
	  mult_big_int maximum_age_sqr (big_int_of_int64 v) (*** always at maximum age during after it is mature and until it is close to unlocked ***)

type hlist = HHash of hashval | HNil | HCons of asset * hlist | HConsH of hashval * hlist

let rec hlist_hashroot hl =
  match hl with
  | HHash(h) -> Some(h)
  | HNil -> None
  | HCons(a,hr) ->
      begin
	match hlist_hashroot hr with
	| None -> Some(hashtag (assetid a) 3l)
	| Some(k) -> Some(hashtag (hashpair (assetid a) k) 4l)
      end
  | HConsH(h,hr) ->
      begin
	match hlist_hashroot hr with
	| None -> Some(hashtag h 3l)
	| Some(k) -> Some(hashtag (hashpair h k) 4l)
      end

type nehlist = NehHash of hashval | NehCons of asset * hlist | NehConsH of hashval * hlist

let nehlist_hlist hl =
  match hl with
  | NehHash(h) -> HHash h
  | NehCons(a,hr) -> HCons(a,hr)
  | NehConsH(h,hr) -> HConsH(h,hr)

let nehlist_hashroot hl =
  match hl with
  | NehHash(h) -> h
  | NehCons(a,hr) ->
      begin
	match hlist_hashroot hr with
	| None -> hashtag (assetid a) 3l
	| Some(k) -> hashtag (hashpair (assetid a) k) 4l
      end
  | NehConsH(h,hr) ->
      begin
	match hlist_hashroot hr with
	| None -> hashtag h 3l
	| Some(k) -> hashtag (hashpair h k) 4l
      end

let rec in_hlist a hl =
  match hl with
  | HCons(b,hr) when a = b -> true
  | HCons(_,hr) -> in_hlist a hr
  | HConsH(_,hr) -> in_hlist a hr
  | _ -> false

let in_nehlist a hl =
  match hl with
  | NehCons(b,hr) when a = b -> true
  | NehCons(_,hr) -> in_hlist a hr
  | NehConsH(_,hr) -> in_hlist a hr
  | _ -> false

let rec hlist_lookup_asset k hl =
  match hl with
  | HCons(a,hr) when assetid a = k -> Some(a)
  | HCons(_,hr) -> hlist_lookup_asset k hr
  | HConsH(_,hr) -> hlist_lookup_asset k hr
  | _ -> None

let nehlist_lookup_asset k hl =
  match hl with
  | NehCons(a,hr) when assetid a = k -> Some(a)
  | NehCons(_,hr) -> hlist_lookup_asset k hr
  | NehConsH(_,hr) -> hlist_lookup_asset k hr
  | _ -> None

let rec hlist_lookup_marker hl =
  match hl with
  | HCons(a,hr) when assetpre a = Marker -> Some(a)
  | HCons(_,hr) -> hlist_lookup_marker hr
  | HConsH(_,hr) -> hlist_lookup_marker hr
  | _ -> None

let nehlist_lookup_marker hl =
  match hl with
  | NehCons(a,hr) when assetpre a = Marker -> Some(a)
  | NehCons(_,hr) -> hlist_lookup_marker hr
  | NehConsH(_,hr) -> hlist_lookup_marker hr
  | _ -> None

let rec hlist_lookup_obj_owner hl =
  match hl with
  | HCons((_,_,_,OwnsObj(beta,r)),hr) -> Some(beta,r)
  | HCons(_,hr) -> hlist_lookup_obj_owner hr
  | HConsH(_,hr) -> hlist_lookup_obj_owner hr
  | _ -> None

let nehlist_lookup_obj_owner hl =
  match hl with
  | NehCons((_,_,_,OwnsObj(beta,r)),hr) -> Some(beta,r)
  | NehCons(_,hr) -> hlist_lookup_obj_owner hr
  | NehConsH(_,hr) -> hlist_lookup_obj_owner hr
  | _ -> None

let rec hlist_lookup_prop_owner hl =
  match hl with
  | HCons((_,_,_,OwnsProp(beta,r)),hr) -> Some(beta,r)
  | HCons(_,hr) -> hlist_lookup_prop_owner hr
  | HConsH(_,hr) -> hlist_lookup_prop_owner hr
  | _ -> None

let nehlist_lookup_prop_owner hl =
  match hl with
  | NehCons((_,_,_,OwnsProp(beta,r)),hr) -> Some(beta,r)
  | NehCons(_,hr) -> hlist_lookup_prop_owner hr
  | NehConsH(_,hr) -> hlist_lookup_prop_owner hr
  | _ -> None

let rec hlist_lookup_neg_prop_owner hl =
  match hl with
  | HCons((_,_,_,OwnsNegProp),hr) -> true
  | HCons(_,hr) -> hlist_lookup_neg_prop_owner hr
  | HConsH(_,hr) -> hlist_lookup_neg_prop_owner hr
  | _ -> false

let nehlist_lookup_neg_prop_owner hl =
  match hl with
  | NehCons((_,_,_,OwnsNegProp),hr) -> true
  | NehCons(_,hr) -> hlist_lookup_neg_prop_owner hr
  | NehConsH(_,hr) -> hlist_lookup_neg_prop_owner hr
  | _ -> false

type ctree =
  | CLeaf of bool list * nehlist
  | CHash of hashval
  | CLeft of ctree
  | CRight of ctree
  | CBin of ctree * ctree

let rec print_ctree_r c n =
  for i = 1 to n do Printf.printf " " done;
  match c with
  | CLeaf(bl,hl) -> Printf.printf "Leaf\n"
  | CHash(h) -> Printf.printf "H %s\n" (hashval_hexstring h)
  | CLeft(c0) -> Printf.printf "L\n"; print_ctree_r c0 (n+1)
  | CRight(c1) -> Printf.printf "R\n"; print_ctree_r c1 (n+1)
  | CBin(c0,c1) -> Printf.printf "B\n"; print_ctree_r c0 (n+1); print_ctree_r c1 (n+1)

let print_ctree c = print_ctree_r c 0

let rec print_hlist hl =
  match hl with
  | HHash(h) -> Printf.printf "...%s...\n" (hashval_hexstring h)
  | HNil -> ()
  | HCons((aid,bday,obl,Currency(v)),hr) ->
      begin
	Printf.printf "%s [%Ld] Currency %Ld\n" (hashval_hexstring aid) bday v;
	print_hlist hr
      end
  | HCons((aid,bday,obl,Bounty(v)),hr) ->
      begin
	Printf.printf "%s [%Ld] Bounty %Ld\n" (hashval_hexstring aid) bday v;
	print_hlist hr
      end
  | HCons((aid,bday,obl,OwnsObj(gamma,Some(r))),hr) ->
      begin
	Printf.printf "%s [%Ld] OwnsObj %s %Ld\n" (hashval_hexstring aid) bday (addr_qedaddrstr (payaddr_addr gamma)) r;
	print_hlist hr
      end
  | HCons((aid,bday,obl,OwnsObj(gamma,None)),hr) ->
      begin
	Printf.printf "%s [%Ld] OwnsObj %s None\n" (hashval_hexstring aid) bday (addr_qedaddrstr (payaddr_addr gamma));
	print_hlist hr
      end
  | HCons((aid,bday,obl,OwnsProp(gamma,Some(r))),hr) ->
      begin
	Printf.printf "%s [%Ld] OwnsProp %s %Ld\n" (hashval_hexstring aid) bday (addr_qedaddrstr (payaddr_addr gamma)) r;
	print_hlist hr
      end
  | HCons((aid,bday,obl,OwnsProp(gamma,None)),hr) ->
      begin
	Printf.printf "%s [%Ld] OwnsProp %s None\n" (hashval_hexstring aid) bday (addr_qedaddrstr (payaddr_addr gamma));
	print_hlist hr
      end
  | HCons((aid,bday,obl,OwnsNegProp),hr) ->
      begin
	Printf.printf "%s [%Ld] OwnsNegProp\n" (hashval_hexstring aid) bday;
	print_hlist hr
      end
  | HCons((aid,bday,obl,RightsObj(gamma,r)),hr) ->
      begin
	Printf.printf "%s [%Ld] RightsObj %s %Ld\n" (hashval_hexstring aid) bday (addr_qedaddrstr (termaddr_addr gamma)) r;
	print_hlist hr
      end
  | HCons((aid,bday,obl,RightsProp(gamma,r)),hr) ->
      begin
	Printf.printf "%s [%Ld] RightsProp %s %Ld\n" (hashval_hexstring aid) bday (addr_qedaddrstr (termaddr_addr gamma)) r;
	print_hlist hr
      end
  | HCons((aid,bday,obl,v),hr) ->
      begin
	Printf.printf "%s [%Ld]\n" (hashval_hexstring aid) bday;
	print_hlist hr
      end
  | HConsH(aid,hr) ->
      begin
	Printf.printf "%s *\n" (hashval_hexstring aid);
	print_hlist hr
      end

let right_trim c s =
  let l = ref ((String.length s) - 1) in
  while (!l > 0 && s.[!l] = c) do
    decr l
  done;
  String.sub s 0 (!l+1)

let fraenks_string v =
  let f = Int64.div v 1000000000000L in
  let d = Int64.sub v f in
  let ds = Int64.to_string d in
  let l = String.length ds in
  if l < 12 then
    right_trim '0' ((Int64.to_string f) ^ "." ^ (String.make (12-l) '0') ^ ds)
  else
    right_trim '0' ((Int64.to_string f) ^ "." ^ ds)

let rec print_hlist_to_buffer sb blkh hl =
  match hl with
  | HHash(h) ->
      Buffer.add_string sb "...";
      Buffer.add_string sb (hashval_hexstring h);
      Buffer.add_string sb "...\n"
  | HNil -> ()
  | HCons((aid,bday,None,Currency(v)),hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	Buffer.add_string sb "] Currency ";
	Buffer.add_string sb (fraenks_string v);
	Buffer.add_string sb "; coinage ";
	Buffer.add_string sb (string_of_big_int (coinage blkh bday None v));
	Buffer.add_char sb '\n';
	print_hlist_to_buffer sb blkh hr
      end
  | HCons((aid,bday,((Some(delta,locktime,b)) as obl),Currency(v)),hr) when b ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	if locktime < blkh then
	  Buffer.add_string sb "] Currency (Reward, Locked) "
	else
	  Buffer.add_string sb "] Currency (Reward) ";
	Buffer.add_string sb (fraenks_string v);
	Buffer.add_string sb " spendable by ";
	Buffer.add_string sb (addr_qedaddrstr (payaddr_addr delta));
	if locktime < blkh then
	  begin
	    Buffer.add_string sb " unlocks at height ";
	    Buffer.add_string sb (Int64.to_string locktime);
	    Buffer.add_string sb " in ";
	    Buffer.add_string sb (Int64.to_string (Int64.sub blkh locktime));
	    Buffer.add_string sb " blocks ";
	  end;
	Buffer.add_string sb "; coinage ";
	Buffer.add_string sb (string_of_big_int (coinage blkh bday obl v));
	Buffer.add_char sb '\n';
	print_hlist_to_buffer sb blkh hr
      end
  | HCons((aid,bday,((Some(delta,locktime,b)) as obl),Currency(v)),hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	if locktime < blkh then
	  Buffer.add_string sb "] Currency (Locked) "
	else
	  Buffer.add_string sb "] Currency ";
	Buffer.add_string sb (fraenks_string v);
	Buffer.add_string sb " spendable by ";
	Buffer.add_string sb (addr_qedaddrstr (payaddr_addr delta));
	if locktime < blkh then
	  begin
	    Buffer.add_string sb " unlocks at height ";
	    Buffer.add_string sb (Int64.to_string locktime);
	    Buffer.add_string sb " in ";
	    Buffer.add_string sb (Int64.to_string (Int64.sub blkh locktime));
	    Buffer.add_string sb " blocks ";
	  end;
	Buffer.add_string sb "; coinage ";
	Buffer.add_string sb (string_of_big_int (coinage blkh bday obl v));
	Buffer.add_char sb '\n';
	print_hlist_to_buffer sb blkh hr
      end
  | HCons((aid,bday,obl,Bounty(v)),hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	Buffer.add_string sb "] Bounty ";
	Buffer.add_string sb (fraenks_string v);
	Buffer.add_char sb '\n';
	print_hlist_to_buffer sb blkh hr
      end
  | HCons((aid,bday,obl,OwnsObj(gamma,Some(r))),hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	Buffer.add_string sb "] owned object ";
	Buffer.add_string sb (addr_qedaddrstr (payaddr_addr gamma));
	Buffer.add_string sb " each right costs ";
	Buffer.add_string sb (fraenks_string r);
	Buffer.add_char sb '\n';
	print_hlist_to_buffer sb blkh hr
      end
  | HCons((aid,bday,obl,OwnsObj(gamma,None)),hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	Buffer.add_string sb "] owned object ";
	Buffer.add_string sb (addr_qedaddrstr (payaddr_addr gamma));
	Buffer.add_string sb " rights cannot be purchased\n";
	print_hlist_to_buffer sb blkh hr
      end
  | HCons((aid,bday,obl,OwnsProp(gamma,Some(r))),hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	Buffer.add_string sb "] owned prop ";
	Buffer.add_string sb (addr_qedaddrstr (payaddr_addr gamma));
	Buffer.add_string sb " each right costs ";
	Buffer.add_string sb (fraenks_string r);
	Buffer.add_char sb '\n';
	print_hlist_to_buffer sb blkh hr
      end
  | HCons((aid,bday,obl,OwnsProp(gamma,None)),hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	Buffer.add_string sb "] owned prop ";
	Buffer.add_string sb (addr_qedaddrstr (payaddr_addr gamma));
	Buffer.add_string sb " rights cannot be purchased\n";
	print_hlist_to_buffer sb blkh hr
      end
  | HCons((aid,bday,obl,OwnsNegProp),hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	Buffer.add_string sb "] owned negation of prop\n";
	print_hlist_to_buffer sb blkh hr
      end
  | HCons((aid,bday,obl,RightsObj(gamma,r)),hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	Buffer.add_string sb "] ";
	Buffer.add_string sb (Int64.to_string r);
	Buffer.add_string sb " rights to use object ";
	Buffer.add_string sb (addr_qedaddrstr (termaddr_addr gamma));
	Buffer.add_char sb '\n';
	print_hlist_to_buffer sb blkh hr
      end
  | HCons((aid,bday,obl,RightsProp(gamma,r)),hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	Buffer.add_string sb "] ";
	Buffer.add_string sb (Int64.to_string r);
	Buffer.add_string sb " rights to use prop ";
	Buffer.add_string sb (addr_qedaddrstr (termaddr_addr gamma));
	Buffer.add_char sb '\n';
	print_hlist_to_buffer sb blkh hr
      end
  | HCons((aid,bday,obl,Marker),hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	Buffer.add_string sb "] Marker\n";
	print_hlist_to_buffer sb blkh hr
      end
  | HCons((aid,bday,obl,TheoryPublication(gamma,nonce,d)),hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	Buffer.add_string sb "] Theory\n";
	print_hlist_to_buffer sb blkh hr
      end
  | HCons((aid,bday,obl,SignaPublication(gamma,nonce,th,d)),hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	Buffer.add_string sb "] Signature\n";
	print_hlist_to_buffer sb blkh hr
      end
  | HCons((aid,bday,obl,DocPublication(gamma,nonce,th,d)),hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " [";
	Buffer.add_string sb (Int64.to_string bday);
	Buffer.add_string sb "] Document\n";
	print_hlist_to_buffer sb blkh hr
      end
  | HConsH(aid,hr) ->
      begin
	Buffer.add_string sb (hashval_hexstring aid);
	Buffer.add_string sb " *\n";
	print_hlist_to_buffer sb blkh hr
      end

let rec print_ctree_all_r c n br =
  for i = 1 to n do Printf.printf " " done;
  match c with
  | CLeaf(bl,hl) -> Printf.printf "Leaf %s\n" (addr_qedaddrstr (bitseq_addr ((List.rev br) @ bl))); print_hlist (nehlist_hlist hl)
  | CHash(h) -> Printf.printf "H %s\n" (hashval_hexstring h)
  | CLeft(c0) -> Printf.printf "L\n"; print_ctree_all_r c0 (n+1) (false::br)
  | CRight(c1) -> Printf.printf "R\n"; print_ctree_all_r c1 (n+1) (true::br)
  | CBin(c0,c1) -> Printf.printf "B\n"; print_ctree_all_r c0 (n+1) (false::br); print_ctree_all_r c1 (n+1) (true::br)

let print_ctree_all c = print_ctree_all_r c 0 []

let print_octree_all_r c n br =
  match c with
  | Some(c) -> print_ctree_all_r c n br
  | None -> ()

let rec ctree_hashroot c =
  match c with
  | CLeaf(bl,hl) ->
      List.fold_right
	(fun b h ->
	  if b then
	    hashopair2 None h
	  else
	    hashopair1 h None
	)
	bl (nehlist_hashroot hl)
  | CHash(h) -> h
  | CLeft(c0) -> hashopair1 (ctree_hashroot c0) None
  | CRight(c1) -> hashopair2 None (ctree_hashroot c1)
  | CBin(c0,c1) -> hashopair1 (ctree_hashroot c0) (Some (ctree_hashroot c1))

let rec ctree_numnodes c =
  match c with
  | CLeaf(_,_) -> 1
  | CHash(_) -> 1
  | CLeft(c) -> 1 + ctree_numnodes c
  | CRight(c) -> 1 + ctree_numnodes c
  | CBin(c0,c1) -> 1 + ctree_numnodes c0 + ctree_numnodes c1

let octree_numnodes oc =
  match oc with
  | None -> 0
  | Some(c) -> ctree_numnodes c

let octree_hashroot c =
  match c with
  | Some(c) -> Some(ctree_hashroot c)
  | None -> None

let rec strip_bitseq_false l =
  match l with
  | [] -> []
  | ((false::bl),x)::r -> (bl,x)::strip_bitseq_false r
  | ((true::bl),x)::r -> strip_bitseq_false r
  | _ -> raise (Failure "bitseq length error")
  
let rec strip_bitseq_true l =
  match l with
  | [] -> []
  | ((true::bl),x)::r -> (bl,x)::strip_bitseq_true r
  | ((false::bl),x)::r -> strip_bitseq_true r
  | _ -> raise (Failure "bitseq length error")

let rec strip_bitseq_false0 l =
  match l with
  | [] -> []
  | (false::bl)::r -> bl::strip_bitseq_false0 r
  | (true::bl)::r -> strip_bitseq_false0 r
  | _ -> raise (Failure "bitseq length error")
  
let rec strip_bitseq_true0 l =
  match l with
  | [] -> []
  | (true::bl)::r -> bl::strip_bitseq_true0 r
  | (false::bl)::r -> strip_bitseq_true0 r
  | _ -> raise (Failure "bitseq length error")

let rec hlist_new_assets nw old =
  match nw with
  | [] -> old
  | a::nwr -> HCons(a,hlist_new_assets nwr old)

let rec remove_assets_hlist hl spent =
  match hl with
  | HCons((h,bh,obl,u) as a,hr) ->
      if List.mem h spent then
	remove_assets_hlist hr spent
      else
	HCons(a,remove_assets_hlist hr spent)
  | HConsH(h,hr) ->
      if List.mem h spent then
	remove_assets_hlist hr spent
      else
	HConsH(h,remove_assets_hlist hr spent)
  | _ -> hl

(** * serialization **)
let rec seo_hlist o hl c =
  match hl with
  | HHash(h) -> (* 00 *)
      let c = o 2 0 c in
      seo_hashval o h c
  | HNil -> (* 01 *)
      let c = o 2 1 c in
      c
  | HCons(a,hr) -> (* 10 *)
      let c = o 2 2 c in
      let c = seo_asset o a c in
      seo_hlist o hr c
  | HConsH(aid,hr) -> (* 11 *)
      let c = o 2 3 c in
      let c = seo_hashval o aid c in
      seo_hlist o hr c

let rec sei_hlist i c =
  let (x,c) = i 2 c in
  if x = 0 then
    let (h,c) = sei_hashval i c in
    (HHash(h),c)
  else if x = 1 then
      (HNil,c)
  else if x = 2 then
    let (a,c) = sei_asset i c in
    let (hr,c) = sei_hlist i c in
    (HCons(a,hr),c)
  else
    let (aid,c) = sei_hashval i c in
    let (hr,c) = sei_hlist i c in
    (HConsH(aid,hr),c)

let seo_nehlist o hl c =
  match hl with
  | NehHash(h) -> (* 0 *)
      let c = o 1 0 c in
      seo_hashval o h c
  | NehCons(a,hr) -> (* 1 0 *)
      let c = o 2 1 c in
      let c = seo_asset o a c in
      seo_hlist o hr c
  | NehConsH(aid,hr) -> (* 1 1 *)
      let c = o 2 3 c in
      let c = seo_hashval o aid c in
      seo_hlist o hr c

let sei_nehlist i c =
  let (x,c) = i 1 c in
  if x = 0 then
    let (h,c) = sei_hashval i c in
    (NehHash(h),c)
  else
    let (y,c) = i 1 c in
    if y = 0 then
      let (a,c) = sei_asset i c in
      let (hr,c) = sei_hlist i c in
      (NehCons(a,hr),c)
    else
      let (aid,c) = sei_hashval i c in
      let (hr,c) = sei_hlist i c in
      (NehConsH(aid,hr),c)

let rec seo_ctree o tr c =
  match tr with
  | CLeaf(bl,hl) -> (* 00 *)
      let c = o 2 0 c in
      let c = seo_list seo_bool o bl c in
      seo_nehlist o hl c
  | CHash(h) -> (* 01 *)
      let c = o 2 1 c in
      seo_hashval o h c
  | CLeft(trl) -> (* 10 0 *)
      let c = o 3 2 c in
      let c = seo_ctree o trl c in
      c
  | CRight(trr) -> (* 10 1 *)
      let c = o 3 6 c in
      let c = seo_ctree o trr c in
      c
  | CBin(trl,trr) -> (* 11 *)
      let c = o 2 3 c in
      let c = seo_ctree o trl c in
      let c = seo_ctree o trr c in
      c

let rec sei_ctree i c =
  let (x,c) = i 2 c in
  if x = 0 then
    let (bl,c) = sei_list sei_bool i c in
    let (hl,c) = sei_nehlist i c in
    (CLeaf(bl,hl),c)
  else if x = 1 then
    let (h,c) = sei_hashval i c in
    (CHash(h),c)
  else if x = 2 then
    let (y,c) = i 1 c in
    let (tr,c) = sei_ctree i c in
    if y = 0 then
      (CLeft(tr),c)
    else
      (CRight(tr),c)
  else
    let (trl,c) = sei_ctree i c in
    let (trr,c) = sei_ctree i c in
    (CBin(trl,trr),c)

let rec reduce_hlist_to_approx al hl =
  match hl with
  | HNil -> HNil
  | HHash(h) -> HHash(h)
  | HCons((h1,bh1,o1,u1),hr) ->
      if al = [] then
	begin
	  match hlist_hashroot hl with
	  | Some h -> HHash(h)
	  | None -> raise (Failure("Impossible"))
	end
      else
	if List.mem h1 al then
	  HCons((h1,bh1,o1,u1),reduce_hlist_to_approx (List.filter (fun z -> not (z = h1)) al) hr)
	else
	  HConsH(h1,reduce_hlist_to_approx al hr)
  | HConsH(h1,hr) ->
      HConsH(h1,reduce_hlist_to_approx al hr)

let save_ctree f tr =
  let ch = open_out_bin f in
  let c = seo_ctree seoc tr (ch,None) in
  seocf c;
  close_out ch

let save_octree f tr =
  let ch = open_out_bin f in
  let c = seo_option seo_ctree seoc tr (ch,None) in
  seocf c;
  close_out ch

let load_ctree f =
  let ch = open_in_bin f in
  let (tr,_) = sei_ctree seic (ch,None) in
  close_in ch;
  tr

let load_octree f =
  let ch = open_in_bin f in
  let (tr,_) = sei_option sei_ctree seic (ch,None) in
  close_in ch;
  tr

let remove_hashed_ctree r =
  let fn = Filename.concat !ctreedatadir (hashval_hexstring r) in
  if Sys.file_exists fn then Sys.remove fn

let ensure_dir_exists d =
  try
    let s = Unix.stat d in
    if not (s.Unix.st_kind = Unix.S_DIR) then
      raise (Failure (d ^ " is not a directory"))
  with
  | Unix.Unix_error(Unix.ENOENT,_,_) -> raise (Failure(d ^ " directory does not exist"))
  | _ -> raise (Failure("Problem with " ^ d))

exception FoundHashval of hashval
exception GettingRemoteData

let save_asset a =
  let aid = assetid a in
  if not (dbexists "qasset" aid) then
    dbput "qasset" aid a (seo_asset seosb)

let rec save_hlist_elements hl =
  match hl with
  | HCons(a,hr) ->
      save_asset a;
      let aid = assetid a in
      let h = save_hlist_elements hr in
      let r =
	match h with
	| None -> hashtag aid 3l
	| Some(k) -> hashtag (hashpair aid k) 4l
      in
      if dbexists "qhcons" r then
	Some(r)
      else
	begin
	  dbput "qhcons" r (aid,h) (seo_prod seo_hashval (seo_option seo_hashval) seosb);
	  Some(r)
	end
  | HConsH(aid,hr) ->
      let h = save_hlist_elements hr in
      let r =
	match h with
	| None -> hashtag aid 3l
	| Some(k) -> hashtag (hashpair aid k) 4l
      in
      if dbexists "qhcons" r then
	Some(r)
      else
	begin
	  dbput "qhcons" r (aid,h) (seo_prod seo_hashval (seo_option seo_hashval) seosb);
	  Some(r)
	end
  | HNil -> None
  | HHash(r) -> Some(r)

let save_nehlist_elements hl =
  match hl with
  | NehCons(a,hr) ->
      save_asset a;
      let aid = assetid a in
      let h = save_hlist_elements hr in
      let r = 
	match h with
	| None -> hashtag aid 3l
	| Some(k) -> hashtag (hashpair aid k) 4l
      in
      if dbexists "qhcons" r then
	r
      else
	begin
	  dbput "qhcons" r (aid,h) (seo_prod seo_hashval (seo_option seo_hashval) seosb);
	  r
	end
  | NehConsH(aid,hr) ->
      let h = save_hlist_elements hr in
      let r = 
	match h with
	| None -> hashtag aid 3l
	| Some(k) -> hashtag (hashpair aid k) 4l
      in
      if dbexists "qhcons" r then
	r
      else
	begin
	  dbput "qhcons" r (aid,h) (seo_prod seo_hashval (seo_option seo_hashval) seosb);
	  r
	end
  | NehHash(r) -> r

let rec ctree_element_a tr i =
  if i > 0 then
    begin
      match tr with
      | CLeaf(_,NehHash(_)) -> true
      | CLeft(tr0) -> ctree_element_a tr0 (i-1)
      | CRight(tr1) -> ctree_element_a tr1 (i-1)
      | CBin(tr0,tr1) -> ctree_element_a tr0 (i-1) && ctree_element_a tr1 (i-1)
      | _ -> false
    end
  else
    match tr with
    | CHash(_) -> true
    | _ -> false

let ctree_element_p tr =
  ctree_element_a tr 9

let rec save_ctree_elements_a tr i =
  if i > 0 then
    match tr with
    | CLeaf(bl,hl) ->
	let h = save_nehlist_elements hl in
	let r = List.fold_right
	    (fun b h ->
	      if b then
		hashopair2 None h
	      else
		hashopair1 h None
	    )
	    bl h
	in
	let tr2 = CLeaf(bl,NehHash(h)) in
	(tr2,r)
    | CLeft(trl) ->
	let (trl2,hl) = save_ctree_elements_a trl (i-1) in
	let r = hashopair1 hl None in
	(CLeft(trl2),r)
    | CRight(trr) ->
	let (trr2,hr) = save_ctree_elements_a trr (i-1) in
	let r = hashopair2 None hr in
	(CRight(trr2),r)
    | CBin(trl,trr) ->
	let (trl2,hl) = save_ctree_elements_a trl (i-1) in
	let (trr2,hr) = save_ctree_elements_a trr (i-1) in
	let r = hashopair1 hl (Some(hr)) in
	(CBin(trl2,trr2),r)
    | CHash(r) -> (tr,r)
  else
    let (tre,r) = save_ctree_elements_a tr 9 in
    if ctree_element_p tre then (*** make sure it's an element before saving it ***)
      if dbexists "qctree" r then
	(CHash(r),r)
      else
	begin
	  dbput "qctree" r tre (seo_ctree seosb);
	  (CHash(r),r)
	end
    else (*** if it isn't an element (presumably because it's only approximating an element) then return the hash root only ***)
      (CHash(r),r)
    
let save_ctree_elements tr =
  let (tre,r) = save_ctree_elements_a tr 0 in
  r

let load_asset h =
  dbget "qasset" h (sei_asset seis)

let get_asset h =
  try
    load_asset h
  with Not_found -> (*** request it and fail ***)
(***
      let (qednetinch,qednetoutch,qedneterrch) = Unix.open_process_full ((qednetd()) ^ " getdata qasset " ^ hh) (Unix.environment()) in
    ignore (Unix.close_process_full (qednetinch,qednetoutch,qedneterrch));
(*    raise (Failure ("could not resolve a needed asset " ^ hh ^ "; requesting from peers")) *)
***)
    raise GettingRemoteData

let load_hcons_element h =
  dbget "qhcons" h (sei_prod sei_hashval (sei_option sei_hashval) seis)

let load_hlist_element h =
  match load_hcons_element h with
  | (aid,Some(k)) -> HConsH(aid,HHash(k))
  | (aid,None) -> HConsH(aid,HNil)

let load_nehlist_element h =
  match load_hcons_element h with
  | (aid,Some(k)) -> NehConsH(aid,HHash(k))
  | (aid,None) -> NehConsH(aid,HNil)

let get_hcons_element h =
  try
    load_hcons_element h
  with Not_found -> (*** request it and fail ***)
(***
    let (qednetinch,qednetoutch,qedneterrch) = Unix.open_process_full ((qednetd()) ^ " getdata qhcons " ^ hh) (Unix.environment()) in
    ignore (Unix.close_process_full (qednetinch,qednetoutch,qedneterrch));
(*    raise (Failure ("could not resolve a needed hcons " ^ hh ^ "; requesting from peers")) *)
***)
    raise GettingRemoteData

let get_hlist_element h =
  match get_hcons_element h with
  | (aid,Some(k)) -> HConsH(aid,HHash(k))
  | (aid,None) -> HConsH(aid,HNil)

let get_nehlist_element h =
  match get_hcons_element h with
  | (aid,Some(k)) -> NehConsH(aid,HHash(k))
  | (aid,None) -> NehConsH(aid,HNil)

let rec ctree_super_element_a tr i =
  if i > 0 then
    begin
      match tr with
      | CLeaf(_,_) -> true
      | CLeft(tr0) -> ctree_super_element_a tr0 (i-1)
      | CRight(tr1) -> ctree_super_element_a tr1 (i-1)
      | CBin(tr0,tr1) -> ctree_super_element_a tr0 (i-1) && ctree_super_element_a tr1 (i-1)
      | _ -> false
    end
  else
    true

(*** A 'superelement' is a ctree with enough information to reduce to an element. ***)
let ctree_super_element_p tr =
  ctree_super_element_a tr 9

let rec super_element_to_element_a tr i =
  if i > 0 then
    begin
      match tr with
      | CLeaf(bl,hl) -> CLeaf(bl,NehHash(nehlist_hashroot hl))
      | CLeft(tr0) -> CLeft(super_element_to_element_a tr0 (i-1))
      | CRight(tr1) -> CRight(super_element_to_element_a tr1 (i-1))
      | CBin(tr0,tr1) -> CBin(super_element_to_element_a tr0 (i-1),super_element_to_element_a tr1 (i-1))
      | _ -> raise (Failure("not a super-element"))
    end
  else
    CHash(ctree_hashroot tr)

let super_element_to_element tr =
  super_element_to_element_a tr 9

let load_ctree_element h =
  dbget "qctree" h (sei_ctree seis)

let get_ctree_element h =
  try
    load_ctree_element h
  with Not_found -> (*** request it and fail ***)
(***
    let (qednetinch,qednetoutch,qedneterrch) = Unix.open_process_full ((qednetd()) ^ " getdata qctree " ^ hh) (Unix.environment()) in
    ignore (Unix.close_process_full (qednetinch,qednetoutch,qedneterrch));
(*    raise (Failure ("could not resolve a needed ctree " ^ hh ^ "; requesting from peers")) *)
***)
    raise GettingRemoteData

let rec octree_S_inv c =
  match c with
  | None -> (None,None)
  | Some(CHash(h)) -> octree_S_inv (Some(get_ctree_element h))
  | Some(CLeaf([],hl)) ->
      raise Not_found
  | Some(CLeaf(false::bl,hl)) -> (Some(CLeaf(bl,hl)),None)
  | Some(CLeaf(true::bl,hl)) -> (None,Some(CLeaf(bl,hl)))
  | Some(CLeft(c0)) -> (Some(c0),None)
  | Some(CRight(c1)) -> (None,Some(c1))
  | Some(CBin(c0,c1)) -> (Some(c0),Some(c1))

let rec tx_octree_trans_ n inpl outpl c =
  if inpl = [] && outpl = [] then
    c
  else if n > 0 then
    begin
      match octree_S_inv c with
      | (c0,c1) ->
	  match
	    tx_octree_trans_ (n-1) (strip_bitseq_false inpl) (strip_bitseq_false outpl) c0,
	    tx_octree_trans_ (n-1) (strip_bitseq_true inpl) (strip_bitseq_true outpl) c1
	  with
	  | None,None -> None
	  | Some(CLeaf(bl,hl)),None -> Some(CLeaf(false::bl,hl))
	  | Some(c0r),None -> Some(CLeft(c0r))
	  | None,Some(CLeaf(bl,hl)) -> Some(CLeaf(true::bl,hl))
	  | None,Some(c1r) -> Some(CRight(c1r))
	  | Some(c0r),Some(c1r) -> Some(CBin(c0r,c1r))
    end
  else
    begin
      let hl =
	begin
	  match c with
	  | Some(CLeaf([],hl)) -> nehlist_hlist hl
	  | None -> HNil
	  | _ -> raise (Failure "not a ctree 0")
	end
      in
      let hl2 = hlist_new_assets (List.map (fun (x,y) -> y) outpl) (remove_assets_hlist hl (List.map (fun (x,y) -> y) inpl)) in
      match hl2 with
      | HNil -> None
      | HHash(h) -> Some(CLeaf([],NehHash(h)))
      | HCons(a,hr) -> Some(CLeaf([],NehCons(a,hr)))
      | HConsH(aid,hr) -> Some(CLeaf([],NehConsH(aid,hr)))
    end

let add_vout bh txh outpl =
  let i = ref 0 in
  let r = ref [] in
  List.iter
    (fun (alpha,(obl,u)) ->
      r := (addr_bitseq alpha,(hashpair txh (hashint32 (Int32.of_int !i)),bh,obl,u))::!r;
      incr i;
    )
    outpl;
  !r

let tx_octree_trans bh tx c =
  let (inpl,outpl) = tx in
  tx_octree_trans_ 162
    (List.map (fun (alpha,h) -> (addr_bitseq alpha,h)) inpl)
    (add_vout bh (hashtx tx) outpl)
    c

let rec txl_octree_trans bh txl c =
  match txl with
  | (tx::txr) -> txl_octree_trans bh txr (tx_octree_trans bh tx c)
  | [] -> c

let rec expand_hlist hl z =
  match hl,z with
  | _,Some(i) when i <= 0 ->
      begin
	match hlist_hashroot hl with
	| Some(h) -> HHash(h)
	| None -> HNil
      end
  | HNil,_ -> HNil
  | HHash(h),_ -> expand_hlist (get_hlist_element h) z
  | HCons(a,hr),None -> HCons(a,expand_hlist hr None)
  | HCons(a,hr),Some(i) -> HCons(a,expand_hlist hr (Some(i-1)))
  | HConsH(aid,hr),None -> HCons(get_asset aid,expand_hlist hr None)
  | HConsH(aid,hr),Some(i) -> HCons(get_asset aid,expand_hlist hr (Some(i-1)))

let rec expand_nehlist hl z =
  match hl,z with
  | _,Some(i) when i <= 0 -> NehHash(nehlist_hashroot hl)
  | NehHash(h),_ -> expand_nehlist (get_nehlist_element h) z
  | NehCons(a,hr),None -> NehCons(a,expand_hlist hr None)
  | NehCons(a,hr),Some(i) -> NehCons(a,expand_hlist hr (Some(i-1)))
  | NehConsH(aid,hr),None -> NehCons(get_asset aid,expand_hlist hr None)
  | NehConsH(aid,hr),Some(i) -> NehCons(get_asset aid,expand_hlist hr (Some(i-1)))

let rec ctree_pre bl c d z =
  match bl with
  | [] ->
      begin
	match c with
	| CLeaf([],hl) -> (Some(expand_nehlist hl z),d)
	| _ -> (None,d)
      end
  | (b::br) ->
      match c with
      | CLeaf(bl2,hl) -> if bl = bl2 then (Some(expand_nehlist hl z),d) else (None,d)
      | CLeft(c0) -> if b then (None,d) else ctree_pre br c0 (d+1) z
      | CRight(c1) -> if b then ctree_pre br c1 (d+1) z else (None,d)
      | CBin(c0,c1) -> if b then ctree_pre br c1 (d+1) z else ctree_pre br c0 (d+1) z
      | CHash(h) -> ctree_pre bl (get_ctree_element h) d z

let ctree_addr alpha c z =
  ctree_pre (addr_bitseq alpha) c 0 z

exception InsufficientInformation

(*** archive_unused_ctrees/remove_unused_ctrees:
    c1 is the ctree at blockheight blkh and c2 is the ctree at blockheight blkh+1.
    Assume blkh+1 has been buried beneath 256 blocks and so is now being included
    as a rolling checkpoint. We can archive/delete subtrees of c1 which do not occur in c2.
    If archiving, put the hashes into 'archive' file along with the blockheight.
    Users can later call a command to actually move or delete the archived files at or up to some
    block height.
    If removing, then delete the files immediately.
 ***)
let add_to_archive ch blkh ha =
   seocf (seo_int64 seoc blkh (ch,None));
   seocf (seo_hashval seoc ha (ch,None))

let rec process_unused_ctrees_1 a c =
   match c with
   | CLeft(cl) ->
     process_unused_ctrees_1 a cl
   | CRight(cr) ->
     process_unused_ctrees_1 a cr
   | CBin(cl,cr) ->
     process_unused_ctrees_1 a cl;
     process_unused_ctrees_1 a cr
   | _ -> ()

let rec process_unused_ctrees_2 a c1 c2 =
   match c1 with
   | CLeft(c1l) ->
     begin
       match c2 with
       | CLeft(c2l) -> process_unused_ctrees_2 a c1l c2l
       | CBin(c2l,c2r) -> process_unused_ctrees_2 a c1l c2l
       | CLeaf((b::bl),hl) when not b -> process_unused_ctrees_2 a c1l (CLeaf(bl,hl))
       | _ -> process_unused_ctrees_1 a c1l
     end
   | CRight(c1r) ->
     begin
       match c2 with
       | CRight(c2r) -> process_unused_ctrees_2 a c1r c2r
       | CBin(c2l,c2r) -> process_unused_ctrees_2 a c1r c2r
       | CLeaf((b::bl),hl) when b -> process_unused_ctrees_2 a c1r (CLeaf(bl,hl))
       | _ -> process_unused_ctrees_1 a c1r
     end
   | CBin(c1l,c1r) ->
     begin
       match c2 with
       | CLeft(c2l) ->
         process_unused_ctrees_2 a c1l c2l;
         process_unused_ctrees_1 a c1r
       | CRight(c2r) ->
         process_unused_ctrees_1 a c1l;
         process_unused_ctrees_2 a c1r c2r
       | CBin(c2l,c2r) ->
         process_unused_ctrees_2 a c1l c2l;
         process_unused_ctrees_2 a c1r c2r
       | CLeaf((b::bl),hl) when not b ->
         process_unused_ctrees_2 a c1l (CLeaf(bl,hl));
         process_unused_ctrees_1 a c1r
       | CLeaf((b::bl),hl) when b ->
         process_unused_ctrees_1 a c1l;
         process_unused_ctrees_2 a c1r (CLeaf(bl,hl))
       | _ ->
         process_unused_ctrees_1 a c1l;
         process_unused_ctrees_1 a c1r
     end
   | _ -> ()

let archive_unused_ctrees blkh c1 c2 =
  ensure_dir_exists !ctreedatadir;
  let fn = Filename.concat !ctreedatadir "archive" in
  if not (Sys.file_exists fn) then
    begin
      let ch = open_out_gen [Open_wronly;Open_binary;Open_creat] 0o644 fn in
      process_unused_ctrees_2 (add_to_archive ch blkh) c1 c2;
      close_out ch      
    end
  else
    begin
      let ch = open_out_gen [Open_wronly;Open_binary;Open_append] 0o644 fn in
      process_unused_ctrees_2 (add_to_archive ch blkh) c1 c2;
      close_out ch      
    end

let remove_unused_ctrees c1 c2 =
   process_unused_ctrees_2 remove_hashed_ctree c1 c2

let ctree_rights_balanced tr alpha ownr rtot1 rtot2 rtot3 outpl =
  match ownr with
  | Some(beta,None) -> (*** Owner does not allow right to use. Rights may have been obtained in the past. ***)
      Int64.add rtot1 rtot2 = rtot3
  | Some(beta,Some(r)) -> (*** Owner possibly requiring royalties (r = 0L if it is free to use) ***)
      if r > 0L then
	let rtot4 = Int64.div (units_sent_to_addr (payaddr_addr beta) outpl) r in
	Int64.add rtot1 rtot2 = Int64.add rtot3 rtot4
      else
	true (*** If it's free to use, people are free to use or create rights as they please. ***)
  | None -> false (*** No owner, in this case we shouldn't even be here ***)

let rec hlist_full_approx hl =
  match hl with
  | HNil -> true
  | HCons(a,hr) -> hlist_full_approx hr
  | HConsH(_,_) -> false
  | HHash(_) -> false

let nehlist_full_approx hl =
  match hl with
  | NehCons(a,hr) -> hlist_full_approx hr
  | NehConsH(_,_) -> false
  | NehHash(_) -> false

let rec ctree_full_approx_addr tr bl =
  match tr with
  | CLeaf(br,hl) when br = bl -> nehlist_full_approx hl
  | CLeaf(_,_) -> true (*** fully approximates because we know it's empty ***)
  | CHash(_) -> false
  | CLeft(trl) ->
      begin
	match bl with
	| (false::br) -> ctree_full_approx_addr trl br
	| _ -> true (*** fully approximates because we know it's empty ***)
      end
  | CRight(trr) ->
      begin
	match bl with
	| (true::br) -> ctree_full_approx_addr trr br
	| _ -> true (*** fully approximates because we know it's empty ***)
      end
  | CBin(trl,trr) ->
      begin
	match bl with
	| (false::br) -> ctree_full_approx_addr trl br
	| (true::br) -> ctree_full_approx_addr trr br
	| [] -> raise (Failure "Level problem") (*** should never happen ***)
      end

let rec ctree_supports_addr tr bl =
  match tr with
  | CLeaf(_,_) -> true
  | CHash(_) -> false
  | CLeft(trl) ->
      begin
	match bl with
	| (false::br) -> ctree_supports_addr trl br
	| _ -> true (*** supports since known to be empty ***)
      end
  | CRight(trr) ->
      begin
	match bl with
	| (true::br) -> ctree_supports_addr trr br
	| _ -> true (*** supports since known to be empty ***)
      end
  | CBin(trl,trr) ->
      begin
	match bl with
	| (false::br) -> ctree_supports_addr trl br
	| (true::br) -> ctree_supports_addr trr br
	| [] -> raise (Failure "Level problem") (*** should never happen ***)
      end

let rec ctree_supports_asset a tr bl =
  match tr with
  | CLeaf(br,hl) when br = bl -> in_nehlist a hl
  | CLeaf(_,_) -> false
  | CHash(h) -> false
  | CLeft(trl) ->
      begin
	match bl with
	| (false::br) -> ctree_supports_asset a trl br
	| _ -> false
      end
  | CRight(trr) ->
      begin
	match bl with
	| (true::br) -> ctree_supports_asset a trr br
	| _ -> false
      end
  | CBin(trl,trr) ->
      begin
	match bl with
	| (false::br) -> ctree_supports_asset a trl br
	| (true::br) -> ctree_supports_asset a trr br
	| [] -> raise (Failure "Level problem") (*** should never happen ***)
      end

let rec ctree_lookup_asset k tr bl =
  match tr with
  | CLeaf(br,hl) when br = bl -> nehlist_lookup_asset k hl
  | CLeaf(_,_) -> None
  | CHash(h) -> None
  | CLeft(trl) ->
      begin
	match bl with
	| (false::br) -> ctree_lookup_asset k trl br
	| _ -> None
      end
  | CRight(trr) ->
      begin
	match bl with
	| (true::br) -> ctree_lookup_asset k trr br
	| _ -> None
      end
  | CBin(trl,trr) ->
      begin
	match bl with
	| (false::br) -> ctree_lookup_asset k trl br
	| (true::br) -> ctree_lookup_asset k trr br
	| [] -> raise (Failure "Level problem") (*** should never happen ***)
      end

let rec ctree_lookup_addr_assets tr bl =
  match tr with
  | CLeaf(br,hl) when br = bl -> (nehlist_hlist hl)
  | CLeaf(_,_) -> HNil
  | CHash(h) -> HNil
  | CLeft(trl) ->
      begin
	match bl with
	| (false::br) -> ctree_lookup_addr_assets trl br
	| _ -> HNil
      end
  | CRight(trr) ->
      begin
	match bl with
	| (true::br) -> ctree_lookup_addr_assets trr br
	| _ -> HNil
      end
  | CBin(trl,trr) ->
      begin
	match bl with
	| (false::br) -> ctree_lookup_addr_assets trl br
	| (true::br) -> ctree_lookup_addr_assets trr br
	| [] -> raise (Failure "Level problem") (*** should never happen ***)
      end

let rec ctree_lookup_marker tr bl =
  match tr with
  | CLeaf(br,hl) when br = bl -> nehlist_lookup_marker hl
  | CLeaf(_,_) -> None
  | CHash(h) -> None
  | CLeft(trl) ->
      begin
	match bl with
	| (false::br) -> ctree_lookup_marker trl br
	| _ -> None
      end
  | CRight(trr) ->
      begin
	match bl with
	| (true::br) -> ctree_lookup_marker trr br
	| _ -> None
      end
  | CBin(trl,trr) ->
      begin
	match bl with
	| (false::br) -> ctree_lookup_marker trl br
	| (true::br) -> ctree_lookup_marker trr br
	| [] -> raise (Failure "Level problem") (*** should never happen ***)
      end

exception NotSupported

let rec ctree_lookup_input_assets inpl tr =
  match inpl with
  | [] -> []
  | (alpha,k)::inpr ->
      match ctree_lookup_asset k tr (addr_bitseq alpha) with
      | Some(a) -> (alpha,a)::ctree_lookup_input_assets inpr tr
      | None -> raise NotSupported

let rec ctree_supports_output_addrs outpl tr =
  match outpl with
  | (alpha,_)::outpr ->
      if ctree_supports_addr tr (addr_bitseq alpha) then
	ctree_supports_output_addrs outpr tr
      else
	raise NotSupported
  | [] -> ()

(*** return the fee (negative) or reward (positive) if supports tx, otherwise raise NotSupported ***)
let ctree_supports_tx_2 tht sigt blkh tx aal al tr =
  let (inpl,outpl) = tx in
  (*** Each output address must be supported. ***)
  ctree_supports_output_addrs outpl tr;
  let objaddrs = obj_rights_mentioned outpl in
  let propaddrs = prop_rights_mentioned outpl in
  let susesobjs = output_signaspec_uses_objs outpl in
  let susesprops = output_signaspec_uses_props outpl in
  let usesobjs = output_doc_uses_objs outpl in
  let usesprops = output_doc_uses_props outpl in
  let createsobjs = output_creates_objs outpl in
  let createsprops = output_creates_props outpl in
  let createsobjsaddrs1 = List.map (fun (th,h,k) -> hashval_term_addr h) createsobjs in
  let createspropsaddrs1 = List.map (fun (th,h) -> hashval_term_addr h) createsprops in
  let createsobjsaddrs2 = List.map (fun (th,h,k) -> hashval_term_addr (hashtag (hashopair2 th (hashpair h k)) 32l)) createsobjs in
  let createspropsaddrs2 = List.map (fun (th,h) -> hashval_term_addr (hashtag (hashopair2 th h) 33l)) createsprops in
  let createsnegpropsaddrs2 = List.map (fun (th,h) -> hashval_term_addr (hashtag (hashopair2 th h) 33l)) (output_creates_neg_props outpl) in
  (*** If an object or prop is included in a signaspec, then it must be royalty-free to use. ***)
  List.iter (fun (alphapure,alphathy) ->
    let hl = ctree_lookup_addr_assets tr (addr_bitseq (termaddr_addr alphapure)) in
    match hlist_lookup_obj_owner hl with
    | Some(_,Some(r)) when r = 0L ->
	begin
	  let hl = ctree_lookup_addr_assets tr (addr_bitseq (termaddr_addr alphathy)) in
	  match hlist_lookup_obj_owner hl with
	  | Some(_,Some(r)) when r = 0L -> ()
	  | _ -> raise NotSupported
	end
    | _ -> raise NotSupported
    )
    susesobjs;
  List.iter (fun (alphapure,alphathy) ->
    let hl = ctree_lookup_addr_assets tr (addr_bitseq (termaddr_addr alphapure)) in
    match hlist_lookup_prop_owner hl with
    | Some(_,Some(r)) when r = 0L ->
	begin
	  let hl = ctree_lookup_addr_assets tr (addr_bitseq (termaddr_addr alphathy)) in
	  match hlist_lookup_prop_owner hl with
	  | Some(_,Some(r)) when r = 0L -> ()
	  | _ -> raise NotSupported
	end
    | _ -> raise NotSupported
    )
    susesprops;
  (*** If rights are consumed in the input, then they must be mentioned in the output. ***)
  List.iter (fun a ->
    match a with
    | (_,_,_,RightsObj(beta,n)) ->
	if not (List.mem beta objaddrs) then
	  raise NotSupported
    | (_,_,_,RightsProp(beta,n)) ->
	if not (List.mem beta propaddrs) then
	  raise NotSupported
    | _ -> ()
	    )
    al;
  (*** ensure rights are balanced ***)
  List.iter (fun alpha ->
    let hl = ctree_lookup_addr_assets tr (addr_bitseq (termaddr_addr alpha)) in
    if hlist_full_approx hl &&
      ctree_rights_balanced tr alpha (hlist_lookup_obj_owner hl)
	(Int64.of_int (count_rights_used usesobjs alpha))
	(rights_out_obj outpl alpha)
	(count_obj_rights al alpha)
	outpl
    then
      ()
    else
      raise NotSupported)
    objaddrs;
  List.iter (fun alpha ->
    let hl = ctree_lookup_addr_assets tr (addr_bitseq (termaddr_addr alpha)) in
    if hlist_full_approx hl &&
      ctree_rights_balanced tr alpha (hlist_lookup_prop_owner hl)
	(Int64.of_int (count_rights_used usesprops alpha))
	(rights_out_prop outpl alpha)
	(count_prop_rights al alpha)
	outpl
    then
      ()
    else
      raise NotSupported)
    propaddrs;
  (*** publications are correct, new, and were declared in advance by placing a marker in the right pubaddr ***)
  let ensure_addr_empty alpha =
    match ctree_lookup_addr_assets tr (addr_bitseq alpha) with
    | HNil -> ()
    | _ -> raise NotSupported
  in
  let spentmarkersjustified = ref [] in
  List.iter
    (fun (alpha,(obl,u)) ->
      match u with
      | TheoryPublication(gamma,nonce,thy) ->
	  begin
	    ensure_addr_empty alpha; (*** make sure the publication is new because otherwise publishing it is pointless ***)
	    try
	      reset_resource_limits();
	      ignore (check_theoryspec thy);
	      match hashtheory (theoryspec_theory thy) with
	      | Some(thyh) ->
		  let beta = hashval_pub_addr (hashpair (hashaddr (payaddr_addr gamma)) (hashpair nonce thyh)) in
		  begin
		    match
		      List.find
			(fun a ->
			  match a with
			  | (h,bday,obl,Marker) -> List.mem (beta,h) inpl && Int64.add bday intention_minage <= blkh
			  | _ -> false
			)
			al
		    with (h,_,_,_) -> spentmarkersjustified := h::!spentmarkersjustified
		  end
	      | None -> raise NotSupported
	    with
	    | CheckingFailure -> raise NotSupported
	    | NonNormalTerm -> raise NotSupported
	    | Not_found -> raise NotSupported
	  end
      | SignaPublication(gamma,nonce,th,sl) ->
	  begin
	    ensure_addr_empty alpha; (*** make sure the publication is new because otherwise publishing it is pointless ***)
	    try
	      let gvtp th h a =
		let alpha = hashval_term_addr (hashtag (hashopair2 th (hashpair h (hashtp a))) 32l) in
		let hl = ctree_lookup_addr_assets tr (addr_bitseq alpha) in
		match hlist_lookup_obj_owner hl with
		| Some(beta,r) -> true
		| None -> false
	      in
	      let gvkn th k =
		let alpha = hashval_term_addr (hashtag (hashopair2 th k) 33l) in
		let hl = ctree_lookup_addr_assets tr (addr_bitseq alpha) in
		match hlist_lookup_prop_owner hl with (*** A proposition has been proven in a theory iff it has an owner. ***)
		| Some(beta,r) -> true
		| None -> false
	      in
	      let thy = ottree_lookup tht th in
	      reset_resource_limits();
	      ignore (check_signaspec gvtp gvkn th thy sigt sl);
	      let slh = hashsigna (signaspec_signa sl) in
	      let beta = hashval_pub_addr (hashpair (hashaddr (payaddr_addr gamma)) (hashpair nonce (hashopair2 th slh))) in
	      begin
		match
		  List.find
		    (fun a ->
		      match a with
		      | (h,bday,obl,Marker) -> List.mem (beta,h) inpl && Int64.add bday intention_minage <= blkh
		      | _ -> false
		    )
		    al
		with (h,_,_,_) -> spentmarkersjustified := h::!spentmarkersjustified
	      end
	    with
	    | CheckingFailure -> raise NotSupported
	    | NonNormalTerm -> raise NotSupported
	    | Not_found -> raise NotSupported
	  end
      | DocPublication(gamma,nonce,th,dl) ->
	  begin
	    ensure_addr_empty alpha; (*** make sure the publication is new because otherwise publishing it is pointless ***)
	    try
	      let gvtp th h a =
		let alpha = hashval_term_addr (hashtag (hashopair2 th (hashpair h (hashtp a))) 32l) in
		let hl = ctree_lookup_addr_assets tr (addr_bitseq alpha) in
		match hlist_lookup_obj_owner hl with
		| Some(beta,r) -> true
		| None -> false
	      in
	      let gvkn th k =
		let alpha = hashval_term_addr (hashtag (hashopair2 th k) 33l) in
		let hl = ctree_lookup_addr_assets tr (addr_bitseq alpha) in
		match hlist_lookup_prop_owner hl with (*** A proposition has been proven in a theory iff it has an owner. ***)
		| Some(beta,r) -> true
		| None -> false
	      in
	      let thy = ottree_lookup tht th in
	      reset_resource_limits();
	      ignore (check_doc gvtp gvkn th thy sigt dl);
	      let beta = hashval_pub_addr (hashpair (hashaddr (payaddr_addr gamma)) (hashpair nonce (hashopair2 th (hashdoc dl)))) in
	      begin
		match
		  List.find
		    (fun a ->
		      match a with
		      | (h,bday,obl,Marker) -> List.mem (beta,h) inpl && Int64.add bday intention_minage <= blkh
		      | _ -> false
		    )
		    al
		with (h,_,_,_) -> spentmarkersjustified := h::!spentmarkersjustified
	      end
	    with
	    | CheckingFailure -> raise NotSupported
	    | NonNormalTerm -> raise NotSupported
	    | Not_found -> raise NotSupported
	  end
      | _ -> ()
    )
    outpl;
  (*** Every spent Marker corresponds to a publication in the output ***)
  List.iter
    (fun (h,bday,obl,u) ->
      match u with
      | Marker ->
	  if not (List.mem h !spentmarkersjustified) then raise NotSupported
      | _ -> ())
    al;
  (*** If an ownership asset is spent in the input, then it must be included as an output.
       Once a termaddr is owned by someone, it must remain owned by someone. ***)
  List.iter
    (fun (alpha,(h,bday,obl,u)) ->
      match u with
      | OwnsObj(beta,r) ->
	  begin
	    try
	      ignore (List.find
			(fun (alpha2,(obl2,u2)) ->
			  alpha = alpha2 &&
			  match u2 with
			  | OwnsObj(beta2,r2) -> true
			  | _ -> false)
			outpl)
	    with Not_found -> raise NotSupported
	  end
      | OwnsProp(beta,r) ->
	  begin
	    try
	      ignore (List.find
			(fun (alpha2,(obl2,u2)) ->
			  alpha = alpha2 &&
			  match u2 with
			  | OwnsProp(beta2,r2) -> true
			  | _ -> false)
			outpl)
	    with Not_found -> raise NotSupported
	  end
      | OwnsNegProp ->
	  begin
	    try
	      ignore (List.find
			(fun (alpha2,(obl2,u2)) ->
			  alpha = alpha2 &&
			  match u2 with
			  | OwnsNegProp -> true
			  | _ -> false)
			outpl)
	    with Not_found -> raise NotSupported
	  end
      | _ -> ()
    )
    aal;
  (*** newly claimed ownership must be new and supported by a document in the tx, and must not be claimed more than once
       (Since the publisher of the document must sign the tx, the publisher agrees to this ownership declaration.)
       Also, ensure that each ownership asset has an explicit obligation for transfering it.
       The p2pkh or p2sh addr in this obligation is the owner in the sense of who can transfer it and who can collect bounties.
       The p2pkh or p2sh addr listed with the asset is the address which must be paid to buy rights to use the object or proposition.
   ***)
  let ownobjclaims = ref [] in
  let ownpropclaims = ref [] in
  let ownnegpropclaims = ref [] in
  let checkoblnonrew obl = (*** for ownership assets: insist on an obligation, or the ownership will not be transferable; also don't allow it to be indicated as a reward ***)
    match obl with
    | Some(_,_,b) when not b -> ()
    | _ -> raise NotSupported
  in
  List.iter
    (fun (alpha,(obl,u)) ->
      match u with
      | OwnsObj(beta,r) ->
	  begin
	    checkoblnonrew obl;
	    try
	      ignore
		(List.find
		   (fun (alpha1,(_,_,_,u1)) ->
		     alpha = alpha1 &&
		     match u1 with
		     | OwnsObj(_,_) -> true
		     | _ -> false)
		   aal); (*** if the ownership is being transferred ***)
	      ownobjclaims := alpha::!ownobjclaims;
	    with Not_found ->
	      (*** if the ownership is being created ***)
	      if (List.mem alpha createsobjsaddrs1 || List.mem alpha createsobjsaddrs2) && not (List.mem alpha !ownobjclaims) then
		let hl = ctree_lookup_addr_assets tr (addr_bitseq alpha) in
		begin
		  ownobjclaims := alpha::!ownobjclaims;
		  match hlist_lookup_obj_owner hl with
		  | Some(beta2,r2) -> raise NotSupported (*** already owned ***)
		  | None -> ()
		end
	      else
		raise NotSupported
	  end
      | OwnsProp(beta,r) -> 
	  begin
	    checkoblnonrew obl;
	    try
	      ignore
		(List.find
		   (fun (alpha1,(_,_,_,u1)) ->
		     alpha = alpha1 &&
		     match u1 with
		     | OwnsProp(beta1,r1) -> true
		     | _ -> false)
		   aal); (*** if the ownership is being transferred ***)
	      ownpropclaims := alpha::!ownpropclaims;
	    with Not_found ->
	      (*** if the ownership is being created ***)
	      if (List.mem alpha createspropsaddrs1 || List.mem alpha createspropsaddrs2) && not (List.mem alpha !ownpropclaims) then
		let hl = ctree_lookup_addr_assets tr (addr_bitseq alpha) in
		begin
		  ownpropclaims := alpha::!ownpropclaims;
		  match hlist_lookup_prop_owner hl with
		  | Some(beta2,r2) -> raise NotSupported (*** already owned ***)
		  | None -> ()
		end
	      else
		raise NotSupported
	  end
      | OwnsNegProp -> 
	  begin
	    checkoblnonrew obl; (*** note that even this one needs to be transferable in order to collect bounties ***)
	    try
	      ignore (List.find (fun (alpha1,(_,_,_,u1)) -> u1 = OwnsNegProp && alpha = alpha1) aal); (*** if the ownership is being transferred ***)
	      ownnegpropclaims := alpha::!ownnegpropclaims;
	    with Not_found ->
	      (*** if the ownership is being created ***)
	      if (List.mem alpha createsnegpropsaddrs2) && not (List.mem alpha !ownnegpropclaims) then
		let hl = ctree_lookup_addr_assets tr (addr_bitseq alpha) in
		begin
		  ownpropclaims := alpha::!ownpropclaims;
		  if hlist_lookup_neg_prop_owner hl then
		    raise NotSupported (*** already owned ***)
		end
	      else
		raise NotSupported
	  end
      | _ -> ()
    )
    outpl;
  (***
      new objects and props must be given ownership by the tx publishing the document.
   ***)
  List.iter (fun (th,tmh,tph) ->
    try
      let ensureowned alpha =
	let hl = ctree_lookup_addr_assets tr (addr_bitseq alpha) in
	match hlist_lookup_obj_owner hl with
	| Some(beta2,r2) -> () (*** already owned ***)
	| None -> (*** Since alpha was listed in full_needed we know alpha really isn't owned here ***)
	    (*** ensure that it will be owned after the tx ***)
	    if not (List.mem alpha !ownobjclaims) then
	      raise Not_found
      in
      let alphapure = hashval_term_addr tmh in
      let alphathy = hashval_term_addr (hashtag (hashopair2 th (hashpair tmh tph)) 32l) in
      ensureowned alphapure;
      ensureowned alphathy
    with Not_found -> raise NotSupported
    )
    createsobjs;
  List.iter (fun (th,tmh) ->
    try
      let ensureowned alpha =
	let hl = ctree_lookup_addr_assets tr (addr_bitseq alpha) in
	match hlist_lookup_prop_owner hl with
	| Some(beta2,r2) -> () (*** already owned ***)
	| None -> (*** Since alpha was listed in full_needed we know alpha really isn't owned here ***)
	    (*** ensure that it will be owned after the tx ***)
	    if not (List.mem alpha !ownpropclaims) then
	      raise Not_found
      in
      let alphapure = hashval_term_addr tmh in
      let alphathy = hashval_term_addr (hashtag (hashopair2 th tmh) 33l) in
      ensureowned alphapure;
      ensureowned alphathy
    with Not_found -> raise NotSupported
    )
    createsprops;
  (*** bounties can be collected by the owners of props or negprops
       To make checking this easy, the ownership asset is spent and recreated unchanged (except the asset id).
       Note that address for the relevant signature is in the obligation of the ownership asset.
       Essentially the ownership gets trivially transfered when the bounty is collected.
       Someone can place bounties on pure propositions, but this is a bad idea.
       Someone else could collect it by creating an inconsistent theory and giving a trivial proof.
       Real bounties should only be placed on propositions within a theory.
   ***)
  List.iter
    (fun (alpha,(h,bday,obl,u)) -> 
      match u with
      | Bounty(v) ->
	  begin
	    try
	      (*** ensure that an owner of the prop or negprop signed the tx because the ownership asset was an input value ***)
	      ignore
		(List.find
		   (fun (alpha2,(h2,bday2,obl2,u2)) -> (*** remember: it's the obligation that determines who signs these; so the obligations tells who the "owners" are for the purpose of collecting bounties ***)
		     alpha = alpha2 &&
		     match u2 with
		     | OwnsProp(beta2,r2) -> true
		     | OwnsNegProp -> true
		     | _ -> false
		   )
		   aal)
	    with Not_found -> raise NotSupported
	  end
      | _ -> ()
    )
    aal;
  (*** finally, return the number of currency units created or destroyed ***)
  Int64.sub (out_cost outpl) (asset_value_sum blkh al)

let ctree_supports_tx tht sigt blkh tx tr =
  let (inpl,outpl) = tx in
  let aal = ctree_lookup_input_assets inpl tr in
  let al = List.map (fun (_,a) -> a) aal in
  ctree_supports_tx_2 tht sigt blkh tx aal al tr

let rec hlist_lub hl1 hl2 =
  match hl1 with
  | HNil -> HNil
  | HHash(_) -> hl2
  | HCons(a1,hr1) ->
      begin
	match hl2 with
	| HNil -> raise (Failure "incompatible hlists")
	| HHash(_) -> hl1
	| HCons(_,hr2) -> HCons(a1,hlist_lub hr1 hr2)
	| HConsH(_,hr2) -> HCons(a1,hlist_lub hr1 hr2)
      end
  | HConsH(h1,hr1) ->
      match hl2 with
      | HNil -> raise (Failure "incompatible hlists")
      | HHash(_) -> hl1
      | HCons(a2,hr2) -> HCons(a2,hlist_lub hr1 hr2)
      | HConsH(_,hr2) -> HConsH(h1,hlist_lub hr1 hr2)

let nehlist_lub hl1 hl2 =
  match hl1 with
  | NehHash(_) -> hl2
  | NehCons(a1,hr1) ->
      begin
	match hl2 with
	| NehHash(_) -> hl1
	| NehCons(_,hr2) -> NehCons(a1,hlist_lub hr1 hr2)
	| NehConsH(_,hr2) -> NehCons(a1,hlist_lub hr1 hr2)
      end
  | NehConsH(h1,hr1) ->
      match hl2 with
      | NehHash(_) -> hl1
      | NehCons(a2,hr2) -> NehCons(a2,hlist_lub hr1 hr2)
      | NehConsH(_,hr2) -> NehConsH(h1,hlist_lub hr1 hr2)

let rec ctreeLinv c =
  match c with
  | CLeaf(bl,hl) -> Some(bl,hl)
  | CLeft(c0) ->
      begin
	match ctreeLinv c0 with
	| Some(bl,hl) -> Some(false::bl,hl)
	| None -> None
      end
  | CRight(c1) ->
      begin
	match ctreeLinv c1 with
	| Some(bl,hl) -> Some(true::bl,hl)
	| None -> None
      end
  | _ -> None

let rec ctree_singlebranch_lub bl hl c =
  match ctreeLinv c with
  | Some(_,hl2) -> CLeaf(bl,nehlist_lub hl hl2)
  | None -> CLeaf(bl,hl)

let rec ctree_lub c1 c2 =
  match c1 with
  | CHash(_) -> c2
  | CLeaf(bl1,hl1) -> ctree_singlebranch_lub bl1 hl1 c2
  | CLeft(c10) ->
      begin
	match c2 with
	| CHash(_) -> c1
	| CLeaf(bl2,hl2) -> ctree_singlebranch_lub bl2 hl2 c1
	| CLeft(c20) -> CLeft (ctree_lub c10 c20)
	| _ -> raise (Failure "no lub for incompatible ctrees")
      end
  | CRight(c11) ->
      begin
	match c2 with
	| CHash(_) -> c1
	| CLeaf(bl2,hl2) -> ctree_singlebranch_lub bl2 hl2 c1
	| CRight(c21) -> CRight (ctree_lub c11 c21)
	| _ -> raise (Failure "no lub for incompatible ctrees")
      end
  | CBin(c10,c11) ->
      begin
	match c2 with
	| CHash(_) -> c1
	| CBin(c20,c21) -> CBin(ctree_lub c10 c20,ctree_lub c11 c21)
	| _ -> raise (Failure "no lub for incompatible ctrees")
      end

let octree_lub oc1 oc2 =
  match (oc1,oc2) with
  | (Some(c1),Some(c2)) ->
      Some(ctree_lub c1 c2)
  | (None,None) -> None
  | _ -> raise (Failure "no lub for incompatible octrees")

let rec load_expanded_ctree_a c i =
  if i > 0 then
    begin
      match c with
      | CLeft(tr0) -> CLeft(load_expanded_ctree_a tr0 (i-1))
      | CRight(tr1) -> CRight(load_expanded_ctree_a tr1 (i-1))
      | CBin(tr0,tr1) -> CBin(load_expanded_ctree_a tr0 (i-1),load_expanded_ctree_a tr1 (i-1))
      | _ -> c
    end
  else
    load_expanded_ctree c
and load_expanded_ctree c =
  try
    let c2 = load_expanded_ctree_a c 9 in
    let r = ctree_hashroot c2 in
    let ce = load_ctree_element r in
    ctree_lub c2 ce
  with Not_found -> c

let load_expanded_octree c =
  match c with
  | Some(c) -> Some(load_expanded_ctree c)
  | None -> None

let rec hlist_reduce_to_min_support aidl hl =
  match aidl with
  | [] ->
      begin
	match hlist_hashroot hl with
	| Some(h) -> HHash(h)
	| None -> HNil
      end
  | _ ->
      begin
	match hl with
	| HCons((h,bh,o,u),hr) ->
	    if List.mem h aidl then
	      HCons((h,bh,o,u),hlist_reduce_to_min_support (List.filter (fun z -> not (z = h)) aidl) hr)
	    else
	      HConsH(h,hlist_reduce_to_min_support aidl hr)
	| HConsH(h,hr) -> (*** lookup asset if needed ***)
	    if List.mem h aidl then
	      HCons(get_asset h,hlist_reduce_to_min_support (List.filter (fun z -> not (z = h)) aidl) hr)
	    else
	      HConsH(h,hlist_reduce_to_min_support aidl hr)
	| HHash(h) -> (*** do a partial lookup ***)
	    hlist_reduce_to_min_support aidl (get_hlist_element h)
	| _ -> hl
      end

let rec get_full_hlist hl =
  match hl with
  | HNil -> HNil
  | HCons(a,hr) -> HCons(a,get_full_hlist hr)
  | HConsH(h,hr) -> HCons(get_asset h,get_full_hlist hr)
  | HHash(h) -> get_full_hlist (get_hlist_element h)

let rec get_full_nehlist hl =
  match hl with
  | NehCons(a,hr) -> NehCons(a,get_full_hlist hr)
  | NehConsH(h,hr) -> NehCons(get_asset h,get_full_hlist hr)
  | NehHash(h) -> get_full_nehlist (get_nehlist_element h)
      
let rec ctree_reduce_to_min_support n inpl outpl full c =
  if n > 0 then
    begin
      if inpl = [] && outpl = [] && full = [] then
	CHash(ctree_hashroot c)
      else
	begin
	  match c with
	  | CLeaf(false::bl,hl) ->
	      begin
		match ctree_reduce_to_min_support (n-1)
		      (strip_bitseq_false inpl)
		      (strip_bitseq_false0 outpl)
		      (strip_bitseq_false0 full)
		      (CLeaf(bl,hl))
		with
		| CLeaf(bl2,hl2) -> CLeaf(false::bl2,hl2)
		| c2 -> CLeft(c2)
	      end
	  | CLeaf(true::bl,hl) ->
	      begin
		match ctree_reduce_to_min_support (n-1)
		      (strip_bitseq_true inpl)
		      (strip_bitseq_true0 outpl)
		      (strip_bitseq_true0 full)
		      (CLeaf(bl,hl))
		with
		| CLeaf(bl2,hl2) -> CLeaf(true::bl2,hl2)
		| c2 -> CRight(c2)
	      end
	  | CLeft(c0) ->
	      CLeft(ctree_reduce_to_min_support (n-1)
		      (strip_bitseq_false inpl)
		      (strip_bitseq_false0 outpl)
		      (strip_bitseq_false0 full)
		      c0)
	  | CRight(c1) ->
	      CRight(ctree_reduce_to_min_support (n-1)
		       (strip_bitseq_true inpl)
		       (strip_bitseq_true0 outpl)
		       (strip_bitseq_true0 full)
		       c1)
	  | CBin(c0,c1) ->
	      CBin(ctree_reduce_to_min_support (n-1)
		     (strip_bitseq_false inpl)
		     (strip_bitseq_false0 outpl)
		     (strip_bitseq_false0 full)
		     c0,
		   ctree_reduce_to_min_support (n-1)
		       (strip_bitseq_true inpl)
		       (strip_bitseq_true0 outpl)
		       (strip_bitseq_true0 full)
		       c1)
	  | CHash(h) -> (*** changed to expand in this case; so the name of the function is misleading ***)
	      ctree_reduce_to_min_support n inpl outpl full (get_ctree_element h)
	  | _ -> c
	end
    end
  else if full = [] then
    begin
      match c with
      | CLeaf([],NehHash(h)) -> 
	  if inpl = [] then
	    c
	  else
	    let aidl = List.map (fun (_,k) -> k) inpl in
	    begin
	      match get_nehlist_element h with
	      | NehConsH(aid,hr) ->
		  if List.mem aid aidl then
		    let a = get_asset aid in
		    CLeaf([],NehCons(a,hlist_reduce_to_min_support (List.filter (fun z -> not (z = aid)) aidl) hr))
		  else
		    CLeaf([],NehConsH(aid,hlist_reduce_to_min_support aidl hr))
	      | _ -> raise (Failure "impossible")
	    end
      | CLeaf([],(NehCons((h,bh,o,u),hr) as hl)) ->
	  if inpl = [] then
	    CLeaf([],NehHash(nehlist_hashroot hl))
	  else
	    let aidl = List.map (fun (_,k) -> k) inpl in
	    if List.mem h aidl then
	      CLeaf([],NehCons((h,bh,o,u),hlist_reduce_to_min_support (List.filter (fun z -> not (z = h)) aidl) hr))
	    else
	      CLeaf([],NehConsH(h,hlist_reduce_to_min_support aidl hr))
      | CLeaf([],(NehConsH(h,hr) as hl)) ->
	  if inpl = [] then
	    CLeaf([],NehHash(nehlist_hashroot hl))
	  else
	    let aidl = List.map (fun (_,k) -> k) inpl in
	    if List.mem h aidl then
	      let a = get_asset h in
	      CLeaf([],NehCons(a,hlist_reduce_to_min_support (List.filter (fun z -> not (z = h)) aidl) hr))
	    else
	      CLeaf([],NehConsH(h,hlist_reduce_to_min_support aidl hr))
      | _ -> raise (Failure "impossible")
    end
  else
    begin
      match c with
      | CLeaf([],hl) -> CLeaf([],get_full_nehlist hl)
      | _ -> raise (Failure "impossible")
    end

let octree_reduce_to_min_support inpl outpl full oc =
  match oc with
  | None -> None
  | Some(c) -> Some (ctree_reduce_to_min_support 162 inpl outpl full c)

let rec full_needed_1 outpl =
  match outpl with
  | [] -> []
  | (_,(o,(RightsObj(beta,_))))::outpr -> addr_bitseq (termaddr_addr beta)::full_needed_1 outpr
  | (_,(o,(RightsProp(beta,_))))::outpr -> addr_bitseq (termaddr_addr beta)::full_needed_1 outpr
  | (alpha,(o,(OwnsObj(_,_))))::outpr -> addr_bitseq alpha::full_needed_1 outpr
  | (alpha,(o,(OwnsProp(_,_))))::outpr -> addr_bitseq alpha::full_needed_1 outpr
  | (_,(o,TheoryPublication(gamma,nonce,thy)))::outpr ->
      let beta = hashval_pub_addr (hashpair (hashaddr (payaddr_addr gamma)) (hashopair1 nonce (hashtheory (theoryspec_theory thy)))) in
      addr_bitseq beta::full_needed_1 outpr
  | (_,(o,SignaPublication(gamma,nonce,th,sl)))::outpr ->
      let beta = hashval_pub_addr (hashpair (hashaddr (payaddr_addr gamma)) (hashpair nonce (hashopair2 th (hashsigna (signaspec_signa sl))))) in
      addr_bitseq beta::full_needed_1 outpr
  | (_,(o,DocPublication(gamma,nonce,th,dl)))::outpr ->
      let beta = hashval_pub_addr (hashpair (hashaddr (payaddr_addr gamma)) (hashpair nonce (hashopair2 th (hashdoc dl)))) in
      addr_bitseq beta::full_needed_1 outpr
  | _::outpr -> full_needed_1 outpr

let full_needed outpl =
  let r = ref (full_needed_1 outpl) in
  List.iter
    (fun (alphapure,alphathy) ->
	r := addr_bitseq (hashval_term_addr alphapure)::addr_bitseq (hashval_term_addr alphathy)::!r)
    (output_signaspec_uses_objs outpl);
  List.iter
    (fun (alphapure,alphathy) ->
	r := addr_bitseq (hashval_term_addr alphapure)::addr_bitseq (hashval_term_addr alphathy)::!r)
    (output_signaspec_uses_props outpl);
  List.iter
    (fun (alphapure,alphathy) ->
	r := addr_bitseq (hashval_term_addr alphapure)::addr_bitseq (hashval_term_addr alphathy)::!r)
    (output_doc_uses_objs outpl);
  List.iter
    (fun (alphapure,alphathy) ->
	r := addr_bitseq (hashval_term_addr alphapure)::addr_bitseq (hashval_term_addr alphathy)::!r)
    (output_doc_uses_props outpl);
  !r

let get_tx_supporting_octree (inpl,outpl) oc =
  octree_reduce_to_min_support
    (List.map (fun (alpha,z) -> (addr_bitseq alpha,z)) inpl)
    (List.map (fun (alpha,(_,_)) -> addr_bitseq alpha) outpl)
    (full_needed outpl)
    oc

let rec get_txl_supporting_octree txl oc =
  match txl with
  | (tx::txr) ->
      octree_lub (get_tx_supporting_octree tx oc) (get_txl_supporting_octree txr oc)
  | [] -> 
      match oc with
      | Some(c) -> Some(CHash(ctree_hashroot c))
      | None -> None

let rec bitseq_prefix bl cl =
  match bl with
  | [] -> true
  | (b::br) ->
      match cl with
      | [] -> false
      | (c::cr) ->
	  if b = c then
	    bitseq_prefix br cr
	  else
	    false

