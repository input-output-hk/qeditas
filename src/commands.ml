(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Config
open Ser
open Hash
open Cryptocurr
open Signat
open Script
open Net

let walletkeys = ref []
let walletp2shs = ref []
let walletendorsements = ref []
let walletwatchaddrs = ref []
let stakingassets = ref []
let storagetrmassets = ref []
let storagedocassets = ref []
  
let read_wallet () =
  let wallfn = Filename.concat !Config.datadir "wallet.dat" in
  if not (Sys.file_exists wallfn) then
    let s = open_out_bin wallfn in
    begin
      output_byte s 0;
      close_out s;
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
	    let (endors,_) = sei_prod4 sei_payaddr sei_payaddr sei_int8 sei_signat seic (s,None) in (*** For each (alpha,beta,esg) beta can use esg to justify signing for alpha; endorsements can be used for spending/moving, but not for staking. ***)
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

let write_wallet () =
  let wallfn = Filename.concat !Config.datadir "wallet.dat" in
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
      seocf (seo_prod4 seo_payaddr seo_payaddr seo_int8 seo_signat seoc endors (s,None)))
    !walletendorsements;
  List.iter
    (fun watchaddr ->
      output_byte s 3;
      seocf (seo_addr seoc watchaddr (s,None)))
    !walletwatchaddrs;
  close_out s

let append_wallet f =
  let wallfn = Filename.concat !Config.datadir "wallet.dat" in
  let s = open_out_gen [Open_append;Open_wronly] 0x660 wallfn in
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
	ignore (List.find (fun (beta,_,_,_) -> beta = (b,x4,x3,x2,x1,x0)) !walletendorsements);
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
	  (fun (alpha2,beta,by0,esg) -> if alpha = payaddr_addr alpha2 then (replwall := true; false) else true)
	  !walletendorsements;
      walletwatchaddrs :=
	List.filter
	  (fun alpha2 -> if alpha = alpha2 then (replwall := true; false) else true)
	  !walletwatchaddrs;
      if !replwall then
	write_wallet()
      else
	append_wallet
	  (fun s ->
	    output_byte s 0;
	    seocf (seo_prod seo_big_int_256 seo_bool seoc (k,b) (s,None)))
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

let printassets () =
  let ctr = Ctre.CAbbrev(hexstring_hashval "7b47514ebb7fb6ab06389940224d09df2951e97e",hexstring_hashval "df418292e7c54837ebdd3962cbfee9d4bc8ca981") in
  Printf.printf "Controlled p2pkh assets:\n";
  List.iter
    (fun (k,b,(x,y),w,h,z) ->
      match Ctre.ctree_addr (hashval_p2pkh_addr h) ctr with
      | (Some(Ctre.CLeaf(_,hl)),_) ->
	  Printf.printf "%s:\n" z;
	  Ctre.print_hlist (Ctre.nehlist_hlist hl)
      | (None,_) ->
	  Printf.printf "%s: empty\n" z;
      | _ ->
	  Printf.printf "%s: no information\n" z;
    )
    !walletkeys;
  Printf.printf "Possibly controlled p2sh assets:\n";
  List.iter
    (fun (h,z,scr) ->
      match Ctre.ctree_addr (hashval_p2sh_addr h) ctr with
      | (Some(Ctre.CLeaf(_,hl)),_) ->
	  Printf.printf "%s:\n" z;
	  Ctre.print_hlist (Ctre.nehlist_hlist hl)
      | (None,_) ->
	  Printf.printf "%s: empty\n" z;
      | _ ->
	  Printf.printf "%s: no information\n" z;
    )
    !walletp2shs;
  Printf.printf "Assets via endorsement:\n";
  List.iter
    (fun (alpha,beta,by0,esg) ->
      let alpha2 = payaddr_addr alpha in
      match Ctre.ctree_addr alpha2 ctr with
      | (Some(Ctre.CLeaf(_,hl)),_) ->
	  Printf.printf "%s:\n" (addr_qedaddrstr alpha2);
	  Ctre.print_hlist (Ctre.nehlist_hlist hl)
      | (None,_) ->
	  Printf.printf "%s: empty\n" (addr_qedaddrstr alpha2);
      | _ ->
	  Printf.printf "%s: no information\n" (addr_qedaddrstr alpha2);
    )
    !walletendorsements;
  Printf.printf "Watched assets:\n";
  List.iter
    (fun alpha ->
      match Ctre.ctree_addr alpha ctr with
      | (Some(Ctre.CLeaf(_,hl)),_) ->
	  Printf.printf "%s:\n" (addr_qedaddrstr alpha);
	  Ctre.print_hlist (Ctre.nehlist_hlist hl)
      | (None,_) ->
	  Printf.printf "%s: empty\n" (addr_qedaddrstr alpha);
      | _ ->
	  Printf.printf "%s: no information\n" (addr_qedaddrstr alpha);
    )
    !walletwatchaddrs
    
(***
let do_rpccom r c =
  match r with
  | AddNode(n) ->
      let (remip,remport,v6) = extract_ip_and_port n in
      if addnode remip remport then
	output_byte c 1
      else
	output_byte c 0
  | GetInfo ->
      let sb = Buffer.create 100 in

      send_string c (Buffer.contents sb)
  | ImportWatchAddr(a) ->
      begin
	try
	  let alpha = qedaddrstr_addr a in
	  let a2 = addr_qedaddrstr alpha in
	  if not (a2 = a) then raise (Failure (a ^ " is not a valid Qeditas address"));
	  if privkey_in_wallet_p alpha then raise (Failure "Not adding as a watch address since the wallet already has the private key for this address.");
	  if endorsement_in_wallet_p alpha then raise (Failure "Not adding as a watch address since the wallet already has an endorsement for this address.");
	  if watchaddr_in_wallet_p alpha then raise (Failure "Watch address is already in wallet.");
	  walletwatchaddrs := alpha::!walletwatchaddrs;
	  write_wallet();
	  output_byte c 1
	with
	| Failure(m) ->
	    output_byte c 0;
	    send_string c m
	| _ ->
	    output_byte c 0;
	    send_string c "Exception raised."
      end
  | ImportPrivKey(w) ->
      begin
      end
  | ImportWatchBtcAddr(a) ->
      begin
	try
	  let alpha = btcaddrstr_addr a in
	  if privkey_in_wallet_p alpha then raise (Failure "Not adding as a watch address since the wallet already has the private key for this address.");
	  if endorsement_in_wallet_p alpha then raise (Failure "Not adding as a watch address since the wallet already has an endorsement for this address.");
	  if watchaddr_in_wallet_p alpha then raise (Failure "Watch address is already in wallet.");
	  let alphaq = addr_qedaddrstr alpha in
	  walletwatchaddrs := alpha::!walletwatchaddrs;
	  write_wallet();
	  output_byte c 1;
	  send_string c alphaq
	with
	| Failure(m) ->
	    output_byte c 0;
	    send_string c m
	| _ ->
	    output_byte c 0;
	    send_string c "Exception raised."
      end
  | ImportBtcPrivKey(w) ->
      begin
	try
	  let (k,b) = privkey_from_btcwif w in
	  match Secp256k1.smulp k Secp256k1._g with
	  | Some(x,y) ->
	      let h = pubkey_hashval (x,y) b in
	      let alpha = Hash.hashval_p2pkh_addr h in
	      let a = addr_qedaddrstr alpha in
	      if privkey_in_wallet_p alpha then raise (Failure "Private key already in wallet.");
	      walletkeys := (k,b,(x,y),qedwif k b,h,a)::!walletkeys;
	      walletendorsements := (*** remove endorsements if the wallet has the private key for the address, since it can now sign directly ***)
		List.filter
		  (fun (alpha2,beta,by0,esg) -> not (alpha = payaddr_addr alpha2))
		  !walletendorsements;
	      walletwatchaddrs :=
		List.filter
		  (fun alpha2 -> not (alpha = alpha2))
		  !walletwatchaddrs;
	      write_wallet();
	      output_byte c 1;
	      send_string c a
	  | None ->
	      raise (Failure "This private key does not give a public key.")
	with
	| Failure(m) ->
	    output_byte c 0;
	    send_string c m
	| _ ->
	    output_byte c 0;
	    send_string c "Exception raised."
      end
  | ImportP2sh(scr) ->
      begin
	try
	  let bl = bytelist_of_hexstring scr in
	  let h = hash160_bytelist bl in
	  let alpha = hashval_p2sh_addr h in
	  let a = addr_qedaddrstr alpha in
	  walletp2shs := (h,a,bl)::!walletp2shs;
	  walletwatchaddrs :=
	    List.filter
	      (fun alpha2 -> not (alpha = alpha2))
	      !walletwatchaddrs;
	  write_wallet();
	  output_byte c 1;
	  send_string c a
	with
	| Failure(m) ->
	    output_byte c 0;
	    send_string c m
	| _ ->
	    output_byte c 0;
	    send_string c "Exception raised."
      end
  | ImportEndorsement(a,b,s) ->
      begin
	try
	  let alpha = qedaddrstr_addr a in
	  let (p,x4,x3,x2,x1,x0) = alpha in
	  if not (p=0) then raise (Failure (a ^ " expected to be a p2pkh address."));
	  let alphap = (false,x4,x3,x2,x1,x0) in
	  if privkey_in_wallet_p alpha then raise (Failure "Not adding endorsement since the wallet already has the private key for this address.");
	  if endorsement_in_wallet_p alpha then raise (Failure "An endorsement for this address is already in the wallet.");
	  let beta = qedaddrstr_addr b in
	  let (q,y4,y3,y2,y1,y0) = beta in
	  if q = 0 && not (privkey_in_wallet_p beta) then raise (Failure ("The private key for " ^ b ^ " must be in the wallet before an endorsement to it can be added."));
	  let betap = (q=1,y4,y3,y2,y1,y0) in
	  let (by0,esg) = decode_signature s in
	  if not (verifybitcoinmessage (x4,x3,x2,x1,x0) by0 esg ("endorse " ^ b)) then
	    raise (Failure "endorsement signature verification failed; not adding endorsement to wallet");
	  walletendorsements := (alphap,betap,by0,esg)::!walletendorsements;
	  write_wallet();
	  output_byte c 1
	with
	| Failure(m) ->
	    output_byte c 0;
	    send_string c m
	| _ ->
	    output_byte c 0;
	    send_string c "Exception raised."
      end
  | _ -> ()
***)
