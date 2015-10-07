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
  
type rpccom =
    Stop
  | AddNode of string
  | GetInfo
  | ImportWatchAddr of string
  | ImportPrivKey of string
  | ImportWatchBtcAddr of string
  | ImportBtcPrivKey of string
  | ImportP2sh of string
  | ImportEndorsement of string * string * string

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

let send_rpccom c r =
  begin
    match r with
    | Stop ->
	output_byte c 0
    | AddNode(n) ->
	output_byte c 1;
	send_string c n
    | GetInfo ->
	output_byte c 2
    | ImportWatchAddr(a) ->
	output_byte c 3;
	send_string c a
    | ImportPrivKey(w) ->
	output_byte c 4;
	send_string c w
    | ImportWatchBtcAddr(a) ->
	output_byte c 5;
	send_string c a
    | ImportBtcPrivKey(w) ->
	output_byte c 6;
	send_string c w
    | ImportP2sh(scr) ->
	output_byte c 7;
	send_string c scr;
    | ImportEndorsement(a,b,s) ->
	output_byte c 8;
	send_string c a;
	send_string c b;
	send_string c s;
    | _ -> ()
  end;
  flush c

let rec_rpccom c =
  let by0 = input_byte c in
  match by0 with
  | 0 -> Stop
  | 1 ->
      let n = rec_string c in
      AddNode(n)
  | 2 -> GetInfo
  | 3 ->
      let a = rec_string c in
      ImportWatchAddr(a)
  | 4 ->
      let w = rec_string c in
      ImportPrivKey(w)
  | 5 ->
      let a = rec_string c in
      ImportWatchBtcAddr(a)
  | 6 ->
      let w = rec_string c in
      ImportBtcPrivKey(w)
  | 7 ->
      let scr = rec_string c in
      ImportP2sh(scr)
  | 8 ->
      let a = rec_string c in
      let b = rec_string c in
      let s = rec_string c in
      ImportEndorsement(a,b,s)
  | _ -> raise (Failure "Unknown rpc command")

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
    let c = (s,None) in
    let (pkeys,c) = sei_list (sei_prod sei_big_int_256 sei_bool) seic c in
    let (p2shscripts,c) = sei_list (sei_list sei_int8) seic c in
    let (endorsements,c) = sei_list (sei_prod4 sei_payaddr sei_payaddr sei_int8 sei_signat) seic c in (*** For each (alpha,beta,esg) beta can use esg to justify signing for alpha; endorsements can be used for spending/moving, but not for staking. ***)
    let (watchaddrs,c) = sei_list sei_addr seic c in
    close_in s;
    walletkeys :=
      List.map
	(fun (k,b) ->
	  match Secp256k1.smulp k Secp256k1._g with
	  | Some(x,y) ->
	      let h = pubkey_hashval (x,y) b in
	      (k,b,(x,y),qedwif k b,h,addr_qedaddrstr (Hash.hashval_p2pkh_addr h))
	  | None ->
	      raise (Failure "A private key in the wallet did not give a public key.")
	)
	pkeys;
    walletp2shs :=
      List.map
	(fun scr ->
	  let h = hash160_bytelist scr in
	  let a = addr_qedaddrstr (hashval_p2sh_addr h) in
	  (h,a,scr))
	p2shscripts;
    walletendorsements := endorsements;
    walletwatchaddrs := watchaddrs

let write_wallet () =
  let wallfn = Filename.concat !Config.datadir "wallet.dat" in
  let s = open_out_bin wallfn in
  let c = (s,None) in
  let c = seo_list (seo_prod seo_big_int_256 seo_bool) seoc (List.map (fun (k,b,_,_,_,_) -> (k,b)) !walletkeys) c in
  let c = seo_list (seo_list seo_int8) seoc (List.map (fun (_,_,scr) -> scr) !walletp2shs) c in
  let c = seo_list (seo_prod4 seo_payaddr seo_payaddr seo_int8 Signat.seo_signat) seoc !walletendorsements c in
  let c = seo_list seo_addr seoc !walletwatchaddrs c in
  seocf c;
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
  | _ -> raise (Failure("not a hexit: " ^ (string_of_int (Char.code x))))

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
      let ctr = Ctre.CAbbrev(hexstring_hashval "7b47514ebb7fb6ab06389940224d09df2951e97e",hexstring_hashval "df418292e7c54837ebdd3962cbfee9d4bc8ca981") in
      Buffer.add_string sb "Controlled p2pkh assets:\n";
      List.iter
	(fun (k,b,(x,y),w,h,z) ->
	  match Ctre.ctree_addr (hashval_p2pkh_addr h) ctr with
	  | (Some(Ctre.CLeaf(_,hl)),_) ->
	      Buffer.add_string sb z;
	      Buffer.add_string sb ":\n";
	      Ctre.print_hlist_to_buffer sb 0L (Ctre.nehlist_hlist hl)
	  | (None,_) ->
	      Buffer.add_string sb z;
	      Buffer.add_string sb ": empty\n";
	  | _ ->
	      Buffer.add_string sb z;
	      Buffer.add_string sb ": no information\n";
	  )
	!walletkeys;
      Buffer.add_string sb "Possibly controlled p2sh assets:\n";
      List.iter
	(fun (h,z,scr) ->
	  match Ctre.ctree_addr (hashval_p2sh_addr h) ctr with
	  | (Some(Ctre.CLeaf(_,hl)),_) ->
	      Buffer.add_string sb z;
	      Buffer.add_string sb ":\n";
	      Ctre.print_hlist_to_buffer sb 0L (Ctre.nehlist_hlist hl)
	  | (None,_) ->
	      Buffer.add_string sb z;
	      Buffer.add_string sb ": empty\n";
	  | _ ->
	      Buffer.add_string sb z;
	      Buffer.add_string sb ": no information\n";
	  )
	!walletp2shs;
      Buffer.add_string sb "Assets via endorsement:\n";
      List.iter
	(fun (alpha,beta,by0,esg) ->
	  let alpha2 = payaddr_addr alpha in
	  match Ctre.ctree_addr alpha2 ctr with
	  | (Some(Ctre.CLeaf(_,hl)),_) ->
	      Buffer.add_string sb (addr_qedaddrstr alpha2);
	      Buffer.add_string sb ":\n";
	      Ctre.print_hlist_to_buffer sb 0L (Ctre.nehlist_hlist hl)
	  | (None,_) ->
	      Buffer.add_string sb (addr_qedaddrstr alpha2);
	      Buffer.add_string sb ": empty\n";
	  | _ ->
	      Buffer.add_string sb (addr_qedaddrstr alpha2);
	      Buffer.add_string sb ": no information\n";
	  )
	!walletendorsements;
      Buffer.add_string sb "Watched assets:\n";
      List.iter
	(fun alpha ->
	  match Ctre.ctree_addr alpha ctr with
	  | (Some(Ctre.CLeaf(_,hl)),_) ->
	      Buffer.add_string sb (addr_qedaddrstr alpha);
	      Buffer.add_string sb ":\n";
	      Ctre.print_hlist_to_buffer sb 0L (Ctre.nehlist_hlist hl)
	  | (None,_) ->
	      Buffer.add_string sb (addr_qedaddrstr alpha);
	      Buffer.add_string sb ": empty\n";
	  | _ ->
	      Buffer.add_string sb (addr_qedaddrstr alpha);
	      Buffer.add_string sb ": no information\n";
	  )
	!walletwatchaddrs;
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
	try
	  let (k,b) = privkey_from_wif w in
	  let w2 = qedwif k b in
	  if not (w2 = w) then raise (Failure (w ^ " is not a valid Qeditas wif"));
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

