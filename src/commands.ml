(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Config
open Hashaux
open Ser
open Sha256
open Hash
open Net
open Cryptocurr
open Signat
open Script
open Assets
open Tx
open Ctre
open Blocktree

let walletkeys = ref []
let walletp2shs = ref []
let walletendorsements = ref []
let walletwatchaddrs = ref []
let stakingassets = ref []
let storagetrmassets = ref []
let storagedocassets = ref []

let recenttxs : (hashval,Tx.stx) Hashtbl.t = Hashtbl.create 100

let load_recenttxs () =
  let fn = Filename.concat (datadir()) "recenttxs" in
  if Sys.file_exists fn then
    let ch = open_in_bin fn in
    try
      while true do
	let ((txid,stau),_) = sei_prod sei_hashval Tx.sei_stx seic (ch,None) in
	Hashtbl.add recenttxs txid stau
      done
    with
    | End_of_file -> close_in ch
    | exc ->
	Printf.printf "Problem in recenttxs file: %s\n" (Printexc.to_string exc);
	close_in ch;;

let unconfirmed_spent_assets : (hashval,hashval) Hashtbl.t = Hashtbl.create 100

let add_to_txpool txid stau =
  Hashtbl.add stxpool txid stau;
  let ((txin,_),_) = stau in
  List.iter (fun (_,h) -> Hashtbl.add unconfirmed_spent_assets h txid) txin

let remove_from_txpool txid =
  try
    let stau = Hashtbl.find stxpool txid in
    Hashtbl.remove stxpool txid;
    let ((txin,_),_) = stau in
    List.iter (fun (_,h) -> Hashtbl.remove unconfirmed_spent_assets h) txin
  with Not_found -> ()

let load_txpool () =
  let fn = Filename.concat (datadir()) "txpool" in
  if Sys.file_exists fn then
    let ch = open_in_bin fn in
    try
      while true do
	let ((txid,stau),_) = sei_prod sei_hashval Tx.sei_stx seic (ch,None) in
	add_to_txpool txid stau
      done
    with
    | End_of_file -> close_in ch
    | exc ->
	Printf.printf "Problem in txpool file: %s\n" (Printexc.to_string exc);
	close_in ch;;

let load_wallet () =
  let wallfn = Filename.concat (datadir()) "wallet" in
  if not (Sys.file_exists wallfn) then
    let s = open_out_bin wallfn in
    begin
      walletkeys := [];
      walletp2shs := [];
      walletendorsements := [];
      walletwatchaddrs := []
    end
  else
    let s = open_in_bin wallfn in
    try
      while true do
	let by = input_byte s in
	match by with
	| 0 ->
	    let ((k,b),_) = sei_prod sei_big_int_256 sei_bool seic (s,None) in
	    walletkeys :=
	      (match Secp256k1.smulp k Secp256k1._g with
	      | Some(x,y) ->
		  let h = pubkey_hashval (x,y) b in
		  let alpha = addr_qedaddrstr (Hash.hashval_p2pkh_addr h) in
		  (k,b,(x,y),qedwif k b,h,alpha)
	      | None ->
		  raise (Failure "A private key in the wallet did not give a public key.")
	      )::!walletkeys
	| 1 ->
	    let (scr,_) = sei_list sei_int8 seic (s,None) in
	    walletp2shs :=
	      (let h = hash160_bytelist scr in
	      let a = addr_qedaddrstr (hashval_p2sh_addr h) in
	      (h,a,scr))::!walletp2shs
	| 2 ->
	    let (endors,_) = sei_prod6 sei_payaddr sei_payaddr (sei_prod sei_big_int_256 sei_big_int_256) sei_varintb sei_bool sei_signat seic (s,None) in (*** For each (alpha,beta,esg) beta can use esg to justify signing for alpha; endorsements can be used for spending/moving, but not for staking. ***)
	    walletendorsements := endors::!walletendorsements
	| 3 ->
	    let (watchaddr,_) = sei_addr seic (s,None) in
	    walletwatchaddrs := watchaddr::!walletwatchaddrs
	| _ ->
	    raise (Failure "Bad entry in wallet file")
      done
    with
    | End_of_file -> close_in s
    | Failure(x) ->
	Printf.printf "Warning: %s\nIgnoring the rest of the wallet file.\n" x; flush stdout;
	close_in s

let save_wallet () =
  let wallfn = Filename.concat (datadir()) "wallet" in
  let s = open_out_bin wallfn in
  List.iter
    (fun (k,b,_,_,_,_) ->
      output_byte s 0;
      seocf (seo_prod seo_big_int_256 seo_bool seoc (k,b) (s,None)))
    !walletkeys;
  List.iter
    (fun (_,_,scr) ->
      output_byte s 1;
      seocf (seo_list seo_int8 seoc scr (s,None)))
    !walletp2shs;
  List.iter
    (fun endors ->
      output_byte s 2;
      seocf (seo_prod6 seo_payaddr seo_payaddr (seo_prod seo_big_int_256 seo_big_int_256) seo_varintb seo_bool seo_signat seoc endors (s,None)))
    !walletendorsements;
  List.iter
    (fun watchaddr ->
      output_byte s 3;
      seocf (seo_addr seoc watchaddr (s,None)))
    !walletwatchaddrs;
  close_out s

let append_wallet f =
  let wallfn = Filename.concat (datadir()) "wallet" in
  let s = open_out_gen [Open_creat;Open_append;Open_wronly;Open_binary] 0o660 wallfn in
  f s;
  close_out s

let addnode remip remport =
  false
(***
let addnode remip remport =
  match !socks with
  | None -> (*** no proxy ***)
      begin
	try
	  let (r,ri,ro) = connectpeer remip remport in
	  true
	with _ ->
	  false
      end
  | Some(s) when s = 4 -> (*** socks4 ***)
      begin
	try
	  let (r,ri,ro) = connectpeer_socks4 !socksport remip remport in
	  true
	with _ -> false
      end
  | Some(s) when s = 5 -> (*** socks5, not yet implemented ***)
      false
  | _ -> (*** unknown ***)
      false
***)

let privkey_in_wallet_p alpha =
  let (p,x4,x3,x2,x1,x0) = alpha in
  if p = 0 then
    begin
      try
	ignore (List.find (fun (_,_,_,_,h,_) -> h = (x4,x3,x2,x1,x0)) !walletkeys);
	true
      with Not_found -> false
    end
  else
    false

let endorsement_in_wallet_p alpha =
  let (p,x4,x3,x2,x1,x0) = alpha in
  if p = 0 || p = 1 then
    let b = (p = 1) in
    begin
      try
	ignore (List.find (fun (beta,_,_,_,_,_) -> beta = (b,x4,x3,x2,x1,x0)) !walletendorsements);
	true
      with Not_found -> false
    end
  else
    false

let endorsement_in_wallet_2_p alpha beta =
  let (p,x4,x3,x2,x1,x0) = alpha in
  let (q,y4,y3,y2,y1,y0) = beta in
  if (p = 0 || p = 1) && (q = 0 || q = 1) then
    let b = (p = 1) in
    let c = (q = 1) in
    begin
      try
	ignore (List.find (fun (alpha2,beta2,_,_,_,_) -> alpha2 = (b,x4,x3,x2,x1,x0) && beta2 = (c,y4,y3,y2,y1,y0)) !walletendorsements);
	true
      with Not_found -> false
    end
  else
    false

let watchaddr_in_wallet_p alpha =
  List.mem alpha !walletwatchaddrs

let hexchar_invi x =
  match x with
  | '0' -> 0
  | '1' -> 1
  | '2' -> 2
  | '3' -> 3
  | '4' -> 4
  | '5' -> 5
  | '6' -> 6
  | '7' -> 7
  | '8' -> 8
  | '9' -> 9
  | 'A' -> 10
  | 'B' -> 11
  | 'C' -> 12
  | 'D' -> 13
  | 'E' -> 14
  | 'F' -> 15
  | 'a' -> 10
  | 'b' -> 11
  | 'c' -> 12
  | 'd' -> 13
  | 'e' -> 14
  | 'f' -> 15
  | _ -> raise (Failure("not a hex: " ^ (string_of_int (Char.code x))))

let hexsubstring_int8 h i =
  (hexchar_invi h.[i]) lsl 4 + (hexchar_invi h.[i+1])

let bytelist_of_hexstring h =
  let l = ref (String.length h) in
  let bl = ref [] in
  l := !l-2;
  while (!l > 0) do
    bl := hexsubstring_int8 h !l::!bl;
    l := !l-2
  done;
  !bl

let btctoqedaddr a =
  let alpha = btcaddrstr_addr a in
  let a2 = addr_qedaddrstr alpha in
  Printf.printf "Qeditas address %s corresponds to Bitcoin address %s\n" a2 a

let importprivkey_real (k,b) =
  match Secp256k1.smulp k Secp256k1._g with
  | Some(x,y) ->
      let h = pubkey_hashval (x,y) b in
      let alpha = Hash.hashval_p2pkh_addr h in
      let a = addr_qedaddrstr alpha in
      let replwall = ref false in
      if privkey_in_wallet_p alpha then raise (Failure "Private key already in wallet.");
      walletkeys := (k,b,(x,y),qedwif k b,h,a)::!walletkeys;
      walletendorsements := (*** remove endorsements if the wallet has the private key for the address, since it can now sign directly ***)
	List.filter
	  (fun (alpha2,beta,(x,y),recid,fcomp,esg) -> if alpha = payaddr_addr alpha2 then (replwall := true; false) else true)
	  !walletendorsements;
      walletwatchaddrs :=
	List.filter
	  (fun alpha2 -> if alpha = alpha2 then (replwall := true; false) else true)
	  !walletwatchaddrs;
      if !replwall then
	save_wallet()
      else
	append_wallet (*** this doesn't work. find out why ***)
	  (fun s ->
	    output_byte s 0;
	    seocf (seo_prod seo_big_int_256 seo_bool seoc (k,b) (s,None)));
      Printf.printf "Imported key for address %s\n" a;
      flush stdout
  | None ->
      raise (Failure "This private key does not give a public key.")

let importprivkey w =
  let (k,b) = privkey_from_wif w in
  let w2 = qedwif k b in
  if not (w2 = w) then raise (Failure (w ^ " is not a valid Qeditas wif"));
  importprivkey_real (k,b)

let importbtcprivkey w =
  let (k,b) = privkey_from_btcwif w in
  importprivkey_real (k,b)

let importendorsement a b s =
  let alpha = qedaddrstr_addr a in
  let beta = qedaddrstr_addr b in
  if endorsement_in_wallet_2_p alpha beta then raise (Failure ("An endorsement from " ^ a ^ " to " ^ b ^ " is already in the wallet."));
  let (q,y4,y3,y2,y1,y0) = beta in
  if q = 0 && not (privkey_in_wallet_p beta) then raise (Failure ("The private key for " ^ b ^ " must be in the wallet before an endorsement to it can be added."));
  let betap = (q=1,y4,y3,y2,y1,y0) in
  let (recid,fcomp,esg) = decode_signature s in
  let (p,x4,x3,x2,x1,x0) = alpha in
  if p = 0 then
    begin
      let alphap = (false,x4,x3,x2,x1,x0) in
      if privkey_in_wallet_p alpha then raise (Failure "Not adding endorsement since the wallet already has the private key for this address.");
      match verifybitcoinmessage_recover (x4,x3,x2,x1,x0) recid fcomp esg ("endorse " ^ b) with
      | None ->
	  if !Config.testnet then
	    begin
	      match verifybitcoinmessage_recover (-629004799l, -157083340l, -103691444l, 1197709645l, 224718539l) recid fcomp esg ("fakeendorsement " ^ b ^ " (" ^ (addr_qedaddrstr alpha) ^ ")") with
	      | None ->
		  raise (Failure "endorsement signature verification failed; not adding endorsement to wallet")
	      | Some(x,y) ->
		  Printf.printf "Fake endorsement acceptable for testnet; adding to wallet.\n";
		  walletendorsements := (alphap,betap,(x,y),recid,fcomp,esg)::!walletendorsements;
		  save_wallet() (*** overkill, should append if possible ***)
	    end
	  else
	    raise (Failure "endorsement signature verification failed; not adding endorsement to wallet")
      | Some(x,y) ->
(*	  Printf.printf "just verified endorsement signature:\naddrhex = %s\nrecid = %d\nfcomp = %s\nesgr = %s\nesgs = %s\nendorse %s\n" (hashval_hexstring (x4,x3,x2,x1,x0)) recid (if fcomp then "true" else "false") (let (r,s) = esg in string_of_big_int r) (let (r,s) = esg in string_of_big_int s) b; flush stdout; *)
	  Printf.printf "Verified endorsement; adding to wallet.\n";
	  walletendorsements := (alphap,betap,(x,y),recid,fcomp,esg)::!walletendorsements;
	  save_wallet() (*** overkill, should append if possible ***)
    end
  else if p = 1 then (*** endorsement by a p2sh address, endorsement can only be checked if the script for alpha is known, so it should have been imported earlier ***)
    begin
      raise (Failure "Code for importing endorsements by a p2sh addresses has not yet been written.")
    end
  else
    raise (Failure (a ^ " expected to be a p2pkh or p2sh Qeditas address."))

let importwatchaddr a =
  let alpha = qedaddrstr_addr a in
  let a2 = addr_qedaddrstr alpha in
  if not (a2 = a) then raise (Failure (a ^ " is not a valid Qeditas address"));
  if privkey_in_wallet_p alpha then raise (Failure "Not adding as a watch address since the wallet already has the private key for this address.");
  if endorsement_in_wallet_p alpha then raise (Failure "Not adding as a watch address since the wallet already has an endorsement for this address.");
  if watchaddr_in_wallet_p alpha then raise (Failure "Watch address is already in wallet.");
  walletwatchaddrs := alpha::!walletwatchaddrs;
  save_wallet() (*** overkill, should append if possible ***)

let importwatchbtcaddr a =
  let alpha = btcaddrstr_addr a in
  let a2 = addr_qedaddrstr alpha in
  Printf.printf "Importing as Qeditas address %s\n" a2;
  if privkey_in_wallet_p alpha then raise (Failure "Not adding as a watch address since the wallet already has the private key for this address.");
  if endorsement_in_wallet_p alpha then raise (Failure "Not adding as a watch address since the wallet already has an endorsement for this address.");
  if watchaddr_in_wallet_p alpha then raise (Failure "Watch address is already in wallet.");
  walletwatchaddrs := alpha::!walletwatchaddrs;
  save_wallet() (*** overkill, should append if possible ***)

let printassets_in_ledger ledgerroot =
  let ctr = Ctre.CHash(ledgerroot) in
  let warned = ref false in
  let waitprinted = ref false in
  let al1 = ref [] in
  let tot1 = ref 0L in
  let al2 = ref [] in
  let tot2 = ref 0L in
  let al3 = ref [] in
  let tot3 = ref 0L in
  let al4 = ref [] in
  let tot4 = ref 0L in
  let numtrys = ref 11 in
  let handler f =
    try
      if !numtrys > 1 then decr numtrys;
      for i = 1 to !numtrys do
	try
	  f();
	  raise Exit
	with GettingRemoteData ->
	  if !netconns = [] then
	    begin (** ignore if there are no connections **)
	      if not !warned then
		begin
		  Printf.printf "Warning: The complete ledger is not in the local database and there are no connections to request missing data.\n";
		  Printf.printf "Some assets in the ledger might not be displayed.\n";
		  warned := true
		end;
	      raise Exit
	    end
	  else
	    begin
	      if not !waitprinted then (Printf.printf "Some data is being requested from remote nodes...please wait a minute or two...\n"; flush stdout; waitprinted := true);
	      Unix.sleep 2;
	    end
      done;
      if not !warned then
	begin
	  Printf.printf "Warning: The complete ledger is not in the local database.\n";
	  Printf.printf "Remote data is being requested, but is taking too long.\n";
	  Printf.printf "Some assets in the ledger might not be displayed.\n";
	  warned := true
	end
    with Exit -> ()
  in
  List.iter
    (fun (k,b,(x,y),w,h,z) ->
      handler (fun () -> al1 := (z,Ctre.ctree_addr true true (hashval_p2pkh_addr h) ctr None)::!al1))
    !walletkeys;
  List.iter
    (fun (h,z,scr) ->
      handler (fun () -> al2 := (z,Ctre.ctree_addr true true (hashval_p2sh_addr h) ctr None)::!al2))
    !walletp2shs;
  List.iter
    (fun (alpha,beta,(x,y),recid,fcomp,esg) -> 
      let alpha2 = payaddr_addr alpha in
      handler (fun () -> al3 := (alpha2,Ctre.ctree_addr true true alpha2 ctr None)::!al3))
    !walletendorsements;
  List.iter
    (fun alpha ->
      handler (fun () -> al4 := (alpha,Ctre.ctree_addr true true alpha ctr None)::!al4))
    !walletwatchaddrs;
  let sumcurr tot a =
    match a with
    | (_,_,_,Currency(v)) -> tot := Int64.add !tot v
    | _ -> ()
  in
  Printf.printf "Assets in ledger with root %s:\n" (hashval_hexstring ledgerroot);
  Printf.printf "Controlled p2pkh assets:\n";
  List.iter
    (fun (z,x) ->
      match x with
      | (Some(hl),_) ->
	  Printf.printf "%s:\n" z;
	  Ctre.print_hlist_gen stdout (Ctre.nehlist_hlist hl) (sumcurr tot1)
      | (None,_) ->
	  Printf.printf "%s: empty\n" z;
      | _ ->
	  Printf.printf "%s: no information\n" z;
    )
    !al1;
  Printf.printf "Possibly controlled p2sh assets:\n";
  List.iter
    (fun (z,x) ->
      match x with
      | (Some(hl),_) ->
	  Printf.printf "%s:\n" z;
	  Ctre.print_hlist_gen stdout (Ctre.nehlist_hlist hl) (sumcurr tot2)
      | (None,_) ->
	  Printf.printf "%s: empty\n" z;
      | _ ->
	  Printf.printf "%s: no information\n" z;
    )
    !al2;
  Printf.printf "Assets via endorsement:\n";
  List.iter
    (fun (alpha2,x) ->
      match x with
      | (Some(hl),_) ->
	  Printf.printf "%s:\n" (addr_qedaddrstr alpha2);
	  Ctre.print_hlist_gen stdout (Ctre.nehlist_hlist hl) (sumcurr tot3)
      | (None,_) ->
	  Printf.printf "%s: empty\n" (addr_qedaddrstr alpha2);
      | _ ->
	  Printf.printf "%s: no information\n" (addr_qedaddrstr alpha2);
    )
    !al3;
  Printf.printf "Watched assets:\n";
  List.iter
    (fun (alpha,x) ->
      match x with
      | (Some(hl),_) ->
	  Printf.printf "%s:\n" (addr_qedaddrstr alpha);
	  Ctre.print_hlist_gen stdout (Ctre.nehlist_hlist hl) (sumcurr tot4)
      | (None,_) ->
	  Printf.printf "%s: empty\n" (addr_qedaddrstr alpha);
      | _ ->
	  Printf.printf "%s: no information\n" (addr_qedaddrstr alpha);
    )
    !al4;
  Printf.printf "Total p2pkh: %s fraenks\n" (fraenks_of_cants !tot1);
  Printf.printf "Total p2sh: %s fraenks\n" (fraenks_of_cants !tot2);
  Printf.printf "Total via endorsement: %s fraenks\n" (fraenks_of_cants !tot3);
  Printf.printf "Total watched: %s fraenks\n" (fraenks_of_cants !tot4)

let printassets () =
  let BlocktreeNode(_,_,_,_,_,ledgerroot,_,_,_,_,_,_,_) = !bestnode in
  printassets_in_ledger ledgerroot

let printasset h =
  try
    let (aid,bday,obl,u) = DbAsset.dbget h in
    Printf.printf "%s [%Ld] %s %s\n" (hashval_hexstring aid) bday (preasset_string u) (obligation_string obl)
  with Not_found ->
    Printf.printf "No asset %s found\n" (hashval_hexstring h)

let printhconselt h =
  try
    let (aid,k) = DbHConsElt.dbget h in
    Printf.printf "assetid %s\n" (hashval_hexstring aid);
    match k with
    | Some(k) -> Printf.printf "next hcons elt %s\n" (hashval_hexstring k)
    | None -> Printf.printf "last on the list\n"
  with Not_found ->
    Printf.printf "No hcons elt %s found\n" (hashval_hexstring h)

let printctreeelt h =
  try
    let c = DbCTreeElt.dbget h in
    print_ctree c
  with Not_found ->
    Printf.printf "No ctree elt %s found\n" (hashval_hexstring h)

let printctreeinfo h =
  try
    let c = DbCTreeElt.dbget h in
    let n = ref 0 in
    let v = ref 0L in
    let b = ref 0L in
    let e = ref 1 in
    let l = ref 0 in
    let a = ref 0 in
    let own = ref 0 in
    let rght = ref 0 in
    let mrk = ref 0 in
    let pub = ref 0 in
    let ah = ref 0 in
    let hh = ref 0 in
    let ch = ref 0 in
    let rec hconseltinfo (aid,k) =
      try
	let (_,_,_,preast) = DbAsset.dbget aid in
	incr a;
	match preast with
	| Currency(u) -> v := Int64.add u !v
	| Bounty(u) -> b := Int64.add u !b
	| OwnsObj(_,_) -> incr own
	| OwnsProp(_,_) -> incr own
	| OwnsNegProp -> incr own
	| RightsObj(_,_) -> incr rght
	| RightsProp(_,_) -> incr rght
	| Marker -> incr mrk
	| _ -> incr pub
      with Not_found ->
	incr ah;
	match k with
	| None -> ()
	| Some(k) ->
	    try
	      hconseltinfo (DbHConsElt.dbget k)
	    with Not_found ->
	      incr hh
    in
    let rec ctreeeltinfo c =
      match c with
      | CHash(h) ->
	  begin
	    try
	      incr e;
	      ctreeeltinfo (DbCTreeElt.dbget h)
	    with Not_found -> incr ch
	  end
      | CLeaf(_,NehHash(h)) ->
	  begin
	    try
	      incr l;
	      hconseltinfo (DbHConsElt.dbget h)
	    with Not_found -> incr hh
	  end
      | CLeaf(_,_) -> raise (Failure "ctree was not an element")
      | CLeft(c0) -> ctreeeltinfo c0
      | CRight(c1) -> ctreeeltinfo c1
      | CBin(c0,c1) -> ctreeeltinfo c0; ctreeeltinfo c1
    in
    ctreeeltinfo c;
    Printf.printf "Number of abstract unknown ctrees %d\n" !ch;
    Printf.printf "Number of abstract unknown hcons elts %d\n" !hh;
    Printf.printf "Number of abstract unknown assets %d\n" !ah;
    Printf.printf "Number of known ctree elts %d\n" !e;
    Printf.printf "Number of known leaves %d\n" !l;
    Printf.printf "Number of known assets %d\n" !a;
    Printf.printf "Number of ownership assets %d\n" !own;
    Printf.printf "Number of rights assets %d\n" !rght;
    Printf.printf "Number of marker assets %d\n" !mrk;
    Printf.printf "Number of publication assets %d\n" !pub;
    Printf.printf "Total cants in known currency assets %Ld\n" !v;
    Printf.printf "Total cants in known bounty assets %Ld\n" !b;
  with Not_found ->
    Printf.printf "No ctree %s found\n" (hashval_hexstring h)
  
let printtx_a (tauin,tauout) =
  let i = ref 0 in
  Printf.printf "Inputs (%d):\n" (List.length tauin);
  List.iter
    (fun (alpha,aid) ->
      Printf.printf "Input %d:%s %s\n" !i (addr_qedaddrstr alpha) (hashval_hexstring aid);
      incr i)
    tauin;      
  i := 0;
  Printf.printf "Outputs (%d):\n" (List.length tauout);
  List.iter
    (fun (alpha,(obl,u)) ->
      Printf.printf "Output %d:%s %s %s\n" !i (addr_qedaddrstr alpha) (preasset_string u) (obligation_string obl);
      incr i)
    tauout

let printtx txid =
  try
    let (tau,_) = Hashtbl.find stxpool txid in
    Printf.printf "Tx %s in pool.\n" (hashval_hexstring txid);
    printtx_a tau
  with Not_found ->
    try
      let tau = DbTx.dbget txid in
      Printf.printf "Tx %s in local database.\n" (hashval_hexstring txid);
      printtx_a tau
    with Not_found ->
      Printf.printf "Unknown tx %s.\n" (hashval_hexstring txid)

let createsplitlocktx ledgerroot alpha beta gamma aid i lkh fee =
  if i <= 0 then raise (Failure ("Cannot split into " ^ (string_of_int i) ^ " assets"));
  let alpha2 = payaddr_addr alpha in
  let ctr = Ctre.CHash(ledgerroot) in
  match ctree_lookup_asset true false aid ctr (addr_bitseq alpha2) with
  | None -> Printf.printf "Could not find asset %s at %s\n" (hashval_hexstring aid) (addr_qedaddrstr alpha2); flush stdout
  | Some(_,bday,obl,Currency(v)) ->
      if v > fee then
	begin
	  let rem = ref (Int64.sub v fee) in
	  let u = Int64.div !rem (Int64.of_int i) in
	  if u > 0L then
	    begin
	      let outl = ref [] in
	      for j = 0 to i-2 do
		outl := (gamma,(Some(beta,lkh,false),Currency(u)))::!outl;
		rem := Int64.sub !rem u
	      done;
	      outl := (gamma,(Some(beta,lkh,false),Currency(!rem)))::!outl;
	      let tau : tx = ([(alpha2,aid)],!outl) in
	      printtx_a tau;
	      let s = Buffer.create 100 in
	      seosbf (seo_stx seosb (tau,([],[])) (s,None));
	      let hs = string_hexstring (Buffer.contents s) in
	      Printf.printf "%s\n" hs
	    end
	  else
	    begin
	      Printf.printf "Asset %s is %s fraenks, which is smaller than %d cants after subtracting the fee of %s\n" (hashval_hexstring aid) (fraenks_of_cants v) i (fraenks_of_cants v); flush stdout
	    end	  
	end
      else
	begin
	  Printf.printf "Asset %s is %s fraenks, which is not greater the fee of %s\n" (hashval_hexstring aid) (fraenks_of_cants v) (fraenks_of_cants v); flush stdout
	end
  | _ -> Printf.printf "Asset %s is not currency.\n" (hashval_hexstring aid); flush stdout

(*** first see if private key for beta is in the wallet; if not check if an endorsement is in the wallet; if not fail ***)
let signtx_p2pkh beta taue =
  try
    let (k,b,(x,y),w,h,z) = List.find (fun (_,_,_,_,h,_) -> h = beta) !walletkeys in
    let r = rand_256() in
    P2pkhSignat(Some(x,y),b,signat_big_int taue k r)
  with Not_found ->
    let (alpha,gamma,(x,y),recid,fcomp,esg) =
      List.find 
	(fun (alpha,gam,_,_,_,_) ->
	  let (p,a4,a3,a2,a1,a0) = alpha in
	  not p && (a4,a3,a2,a1,a0) = beta)
	!walletendorsements
    in
    let (p,c4,c3,c2,c1,c0) = gamma in
    if p then
      raise (Failure "p2psh signing not yet supported")
    else
      let (k,b2,(x2,y2),w,h,z) = List.find (fun (_,_,_,_,h,_) -> h = (c4,c3,c2,c1,c0)) !walletkeys in
      let r = rand_256() in
      let s1 = signat_big_int taue k r in
      let s = EndP2pkhToP2pkhSignat(Some(x,y),fcomp,Some(x2,y2),b2,esg,s1) in
      s

let getsig s rl =
  match s with
  | GenSignatReal(s) -> (s,fun gam -> (gam,Some(s))::rl)
  | GenSignatRef(i) -> (*** only allow up to 64K signatures on the list; should be much less than this in practice ***)
      if i < 65535 && i >= 0 then
	match List.nth rl i with
	| (gam,Some(s)) -> (s,fun _ -> rl)
	| (gam,None) -> raise BadOrMissingSignature
      else
	raise BadOrMissingSignature

let rec assoc_pos b l p =
  match l with
  | ((x,v)::r) when x = b -> (v,p)
  | (_::r) -> assoc_pos b r (p+1)
  | [] -> raise Not_found

let rec signtx_ins taue inpl al outpl sl rl (rsl:gensignat_or_ref option list) ci =
  match inpl,al with
  | (alpha,k)::inpr,(a::ar) ->
      begin
	if not (assetid a = k) then raise (Failure "Asset mismatch when trying to sign inputs");
	match assetpre a with
	| Marker -> signtx_ins taue inpr ar outpl sl rl rsl ci
	| Bounty(_) -> signtx_ins taue inpr ar outpl sl rl rsl ci
	| _ ->
	    let obl = assetobl a in
	    match sl with
	    | [] -> signtx_ins taue inpl al outpl [None] rl rsl ci
	    | (None::sr) -> (*** missing signature ***)
		begin
		  (*** check if one of the existing signatures can be used for this ***)
		  try
		    let beta =
		      match obl with
		      | None ->
			  let (p,a4,a3,a2,a1,a0) = alpha in
			  (p=1,a4,a3,a2,a1,a0)
		      | Some(beta,_,_) -> beta
		    in
		    match assoc_pos beta rl 0 with
		    | (Some(s),p) ->
			signtx_ins taue inpr ar outpl sr rl (Some(GenSignatRef(p))::rsl) ci
		    | (None,p) -> raise Not_found
		  with Not_found ->
		    (*** otherwise, try to sign for this input ***)
		    match obl with
		    | Some(beta,lkh,r) ->
			let (p,b4,b3,b2,b1,b0) = beta in
			if p then
			  raise (Failure "p2sh signing is not yet supported")		  
			else
			  begin
			    try
			      let s = signtx_p2pkh (b4,b3,b2,b1,b0) taue in
			      signtx_ins taue inpr ar outpl sr ((beta,Some(s))::rl) (Some(GenSignatReal(s))::rsl) ci
			    with _ ->
			      signtx_ins taue inpr ar outpl sr ((beta,None)::rl) (None::rsl) false
			  end
		  | None ->
		      if p2pkhaddr_p alpha then
			let (_,a4,a3,a2,a1,a0) = alpha in
			begin
			  try
			    let s = signtx_p2pkh (a4,a3,a2,a1,a0) taue in
			    signtx_ins taue inpr ar outpl sr (((false,a4,a3,a2,a1,a0),Some(s))::rl) (Some(GenSignatReal(s))::rsl) ci
			  with _ ->
			    signtx_ins taue inpr ar outpl sr (((false,a4,a3,a2,a1,a0),None)::rl) (None::rsl) false
			end
		      else if p2shaddr_p alpha then
			raise (Failure "p2sh signing is not yet supported")
		      else
			raise (Failure "tx attempts to spend a non-Marker and non-Bounty without an explicit obligation from an address other than a pay address")

		end
	    | (Some(s)::sr) ->
		try
		  let (s1,rl1) = getsig s rl in
		  let blkh = match obl with Some(_,lkh,_) -> lkh | None -> 1L in (*** artificial block height just for checking signatures ***)
		  if check_spend_obligation alpha blkh taue s1 obl then
		    begin
		      match obl with
		      | None -> 
			  let (p,a4,a3,a2,a1,a0) = alpha in
			  signtx_ins taue inpr ar outpl sr (rl1 (p=1,a4,a3,a2,a1,a0)) (Some(GenSignatReal(s1))::rsl) ci
		      | Some(gam,_,_) ->
			  signtx_ins taue inpr ar outpl sr (rl1 gam) (Some(GenSignatReal(s1))::rsl) ci
		    end
		  else if check_move_obligation alpha taue s1 obl (assetpre a) outpl then
		    let (p,a4,a3,a2,a1,a0) = alpha in
		    signtx_ins taue inpr ar outpl sr (rl1 (p=1,a4,a3,a2,a1,a0)) (Some(GenSignatReal(s1))::rsl) ci
		  else
		    raise (Failure "bad signature already part of stx")
		with BadOrMissingSignature ->
		  raise (Failure "bad signature already part of stx")
      end
  | [],[] -> if sl = [] then (List.rev rsl,ci) else raise (Failure "extra unused signature")
  | _,_ -> raise (Failure "problem signing inputs")

let rec signtx_outs taue outpl sl rl rsl co =
  match outpl with
  | (_,(_,TheoryPublication(alpha,n,thy)))::outpr ->
      raise (Failure "to do: write signtx_outs")
  | (_,(_,SignaPublication(alpha,n,th,si)))::outpr ->
      raise (Failure "to do: write signtx_outs")
  | (_,(_,DocPublication(alpha,n,th,si)))::outpr ->
      raise (Failure "to do: write signtx_outs")
  | _::outpr -> signtx_outs taue outpr sl rl rsl co
  | [] -> (List.rev rsl,co)

let signtx lr taustr =
  let s = hexstring_string taustr in
  let (((tauin,tauout) as tau,(tausgin,tausgout) as tausg),_) = sei_stx seis (s,String.length s,None,0,0) in (*** may be partially signed ***)
  let al = List.map (fun (aid,a) -> a) (ctree_lookup_input_assets true false tauin (CHash(lr))) in
  let tauh = hashtx tau in
  let tauh2 = if !Config.testnet then hashtag tauh 288l else tauh in
  let taue = hashval_big_int tauh2 in
  let (tausgin1,ci) = signtx_ins taue tauin al tauout tausgin [] [] true in
  let (tausgout1,co) = signtx_outs taue tauout tausgout [] [] true in
  let stau = (tau,(tausgin1,tausgout1)) in
  let s = Buffer.create 100 in
  seosbf (seo_stx seosb (tau,(tausgin1,tausgout1)) (s,None));
  let hs = string_hexstring (Buffer.contents s) in
  Printf.printf "%s\n" hs;
  if ci && co then
    Printf.printf "Completely signed.\n"
  else
    Printf.printf "Partially signed.\n"

let savetxtopool blkh lr staustr =
  let s = hexstring_string staustr in
  let (((tauin,tauout) as tau,tausg),_) = sei_stx seis (s,String.length s,None,0,0) in
  if tx_valid tau then
    let al = List.map (fun (aid,a) -> a) (ctree_lookup_input_assets true false tauin (CHash(lr))) in
    if tx_signatures_valid blkh al (tau,tausg) then
      let txh = hashtx tau in
      let ch = open_out_gen [Open_creat;Open_append;Open_wronly;Open_binary] 0o660 (Filename.concat (datadir()) "txpool") in
      seocf (seo_prod seo_hashval seo_stx seoc (txh,(tau,tausg)) (ch,None));
      close_out ch
    else
      Printf.printf "Invalid or incomplete signatures\n"
  else
    Printf.printf "Invalid tx\n"

let sendtx blkh lr staustr =
  let s = hexstring_string staustr in
  let (((tauin,tauout) as tau,tausg) as stau,_) = sei_stx seis (s,String.length s,None,0,0) in
  if tx_valid tau then
    let al = List.map (fun (aid,a) -> a) (ctree_lookup_input_assets true false tauin (CHash(lr))) in
    if tx_signatures_valid blkh al (tau,tausg) then
      let txh = hashtx tau in
      let ch = open_out_gen [Open_creat;Open_append;Open_wronly;Open_binary] 0o660 (Filename.concat (datadir()) "txpool") in
      seocf (seo_prod seo_hashval seo_stx seoc (txh,(tau,tausg)) (ch,None));
      close_out ch;
      publish_stx txh stau;
      Printf.printf "%s\n" (hashval_hexstring txh);
      flush stdout;
    else
      Printf.printf "Invalid or incomplete signatures\n"
  else
    Printf.printf "Invalid tx\n"
