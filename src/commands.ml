(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Config
open Ser
open Hash
open Cryptocurr
open Signat
open Script
open Ctre
open Net

let walletkeys = ref []
let walletp2shs = ref []
let walletendorsements = ref []
let walletwatchaddrs = ref []
let stakingassets = ref []
let storagetrmassets = ref []
let storagedocassets = ref []

(***
let load_currentframe () =
  let framefn = Filename.concat (datadir()) "currentframe" in
  if not (Sys.file_exists framefn) then
    (*** default frame, the one used for the initial distribution; only supporting this frame for now; FAbbrev(FBin(FBin(f,f),FAll)) where f is FAbbrev(FBin^8(FAbbrev(FBin^8(FAll)))) ***)
    let (fr,_) = Ctre.sei_frame Ser.seis ("\249\178m\219\150m\219\182\180",9,None,0,0) in
    fr
  else
    let s = open_in_bin framefn in
    let (fr,_) = sei_frame seic (s,None) in
    close_in s;
    fr

let save_currentframe fr =
  let framefn = Filename.concat (datadir()) "currentframe" in
  let s = open_out_bin framefn in
  let _ = seocf (seo_frame seoc fr (s,None)) in
  close_out s
***)
  
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

let txpool : (hashval,Tx.stx) Hashtbl.t = Hashtbl.create 100

let load_txpool () =
  let fn = Filename.concat (datadir()) "txpool" in
  if Sys.file_exists fn then
    let ch = open_in_bin fn in
    try
      while true do
	let ((txid,stau),_) = sei_prod sei_hashval Tx.sei_stx seic (ch,None) in
	Hashtbl.add txpool txid stau
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
  let s = open_out_gen [Open_append;Open_wronly;Open_binary] 0x660 wallfn in
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
      | None -> raise (Failure "endorsement signature verification failed; not adding endorsement to wallet")
      | Some(x,y) ->
	  Printf.printf "just verified endorsement signature:\naddrhex = %s\nrecid = %d\nfcomp = %s\nesgr = %s\nesgs = %s\nendorse %s\n" (hashval_hexstring (x4,x3,x2,x1,x0)) recid (if fcomp then "true" else "false") (let (r,s) = esg in string_of_big_int r) (let (r,s) = esg in string_of_big_int s) b; flush stdout;
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

let rec printassets_a ctr =
  try
    let al1 = List.map (fun (k,b,(x,y),w,h,z) -> (z,Ctre.ctree_addr (hashval_p2pkh_addr h) ctr None)) !walletkeys in
    let al2 = List.map (fun (h,z,scr) -> (z,Ctre.ctree_addr (hashval_p2sh_addr h) ctr None)) !walletp2shs in
    let al3 = List.map (fun (alpha,beta,(x,y),recid,fcomp,esg) -> let alpha2 = payaddr_addr alpha in (alpha2,Ctre.ctree_addr alpha2 ctr None)) !walletendorsements in
    let al4 = List.map (fun alpha -> (alpha,Ctre.ctree_addr alpha ctr None)) !walletwatchaddrs in
    Printf.printf "Controlled p2pkh assets:\n";
    List.iter
      (fun (z,x) ->
	match x with
	| (Some(hl),_) ->
	    Printf.printf "%s:\n" z;
	    Ctre.print_hlist (Ctre.nehlist_hlist hl)
	| (None,_) ->
	    Printf.printf "%s: empty\n" z;
	| _ ->
	    Printf.printf "%s: no information\n" z;
      )
      al1;
    Printf.printf "Possibly controlled p2sh assets:\n";
    List.iter
      (fun (z,x) ->
	match x with
	| (Some(hl),_) ->
	    Printf.printf "%s:\n" z;
	    Ctre.print_hlist (Ctre.nehlist_hlist hl)
	| (None,_) ->
	    Printf.printf "%s: empty\n" z;
	| _ ->
	    Printf.printf "%s: no information\n" z;
      )
      al2;
    Printf.printf "Assets via endorsement:\n";
    List.iter
      (fun (alpha2,x) ->
	match x with
	| (Some(hl),_) ->
	    Printf.printf "%s:\n" (addr_qedaddrstr alpha2);
	    Ctre.print_hlist (Ctre.nehlist_hlist hl)
	| (None,_) ->
	    Printf.printf "%s: empty\n" (addr_qedaddrstr alpha2);
	| _ ->
	    Printf.printf "%s: no information\n" (addr_qedaddrstr alpha2);
      )
      al3;
    Printf.printf "Watched assets:\n";
    List.iter
      (fun (alpha,x) ->
	match x with
	| (Some(hl),_) ->
	    Printf.printf "%s:\n" (addr_qedaddrstr alpha);
	    Ctre.print_hlist (Ctre.nehlist_hlist hl)
	| (None,_) ->
	    Printf.printf "%s: empty\n" (addr_qedaddrstr alpha);
	| _ ->
	    Printf.printf "%s: no information\n" (addr_qedaddrstr alpha);
      )
      al4;
  with Ctre.GettingRemoteData ->
    Printf.printf "Requesting remote data...please wait...\n"; flush stdout;
    Unix.sleep 2;
    printassets_a ctr
  
let printassets () =
  let BlocktreeNode(_,_,_,_,_,ledgerroot,_,_,_,_,_,_,_,_,_) = !bestnode in
  Printf.printf "cr %s\n" (hashval_hexstring ledgerroot); flush stdout;
  let ctr = Ctre.CHash(ledgerroot) in
  printassets_a ctr

    
