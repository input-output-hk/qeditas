(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Config
open Ser
open Hash
open Signat
open Net

let walletkeys = ref []
let walletendorsements = ref []
let walletwatchaddrs = ref []
  
type rpccom =
    Stop
  | AddNode of string
  | GetInfo
  | ImportWatchAddr of string
  | ImportPrivKey of string

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
  | _ -> raise (Failure "Unknown rpc command")

let read_wallet () =
  let wallfn = Filename.concat !Config.datadir "wallet.dat" in
  if not (Sys.file_exists wallfn) then
    let s = open_out_bin wallfn in
    begin
      output_byte s 0;
      close_out s;
      walletkeys := [];
      walletendorsements := [];
      walletwatchaddrs := []
    end
  else
    let s = open_in_bin wallfn in
    let c = (s,None) in
    let (pkeys,c) = sei_list (sei_prod sei_big_int_256 sei_bool) seic c in
    let (endorsements,c) = sei_list (sei_prod3 sei_payaddr sei_payaddr sei_signat) seic c in (*** For each (alpha,beta,esg) beta can use esg to justify signing for alpha; endorsements can be used for spending/moving, but not for staking. ***)
    let (watchaddrs,c) = sei_list sei_addr seic c in
    close_in s;
    walletkeys :=
      List.map
	(fun (k,b) ->
	  match Secp256k1.smulp k Secp256k1._g with
	  | Some(x,y) ->
	      let h = Cryptocurr.pubkey_hashval (x,y) b in
	      (k,b,(x,y),Cryptocurr.qedwif k b,h,Cryptocurr.addr_qedaddrstr (Hash.hashval_p2pkh_addr h))
	  | None ->
	      raise (Failure "A private key in the wallet did not give a public key.")
	)
	pkeys;
    walletendorsements := endorsements;
    walletwatchaddrs := watchaddrs

let write_wallet () =
  let wallfn = Filename.concat !Config.datadir "wallet.dat" in
  let s = open_out_bin wallfn in
  let c = (s,None) in
  let c = seo_list (seo_prod seo_big_int_256 seo_bool) seoc (List.map (fun (k,b,_,_,_,_) -> (k,b)) !walletkeys) c in
  let c = seo_list (seo_prod3 seo_payaddr seo_payaddr Signat.seo_signat) seoc !walletendorsements c in
  let c = seo_list seo_addr seoc !walletwatchaddrs c in
  seocf c;
  close_out s

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

let do_rpccom r c =
  match r with
  | AddNode(n) ->
      let (remip,remport) = extract_ip_and_port n in
      if addnode remip remport then
	output_byte c 1
      else
	output_byte c 0
  | GetInfo ->
      let sb = Buffer.create 100 in
      let ctr = Ctre.CAbbrev(hexstring_hashval "7b47514ebb7fb6ab06389940224d09df2951e97e",hexstring_hashval "df418292e7c54837ebdd3962cbfee9d4bc8ca981") in
      Buffer.add_string sb "Controlled p2pkh Assets:\n";
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
      Buffer.add_string sb "Assets via Endorsement:\n";
      List.iter
	(fun (alpha,beta,esg) ->
	  let alpha2 = payaddr_addr alpha in
	  match Ctre.ctree_addr alpha2 ctr with
	  | (Some(Ctre.CLeaf(_,hl)),_) ->
	      Buffer.add_string sb (Cryptocurr.addr_qedaddrstr alpha2);
	      Buffer.add_string sb ":\n";
	      Ctre.print_hlist_to_buffer sb 0L (Ctre.nehlist_hlist hl)
	  | (None,_) ->
	      Buffer.add_string sb (Cryptocurr.addr_qedaddrstr alpha2);
	      Buffer.add_string sb ": empty\n";
	  | _ ->
	      Buffer.add_string sb (Cryptocurr.addr_qedaddrstr alpha2);
	      Buffer.add_string sb ": no information\n";
	  )
	!walletendorsements;
      Buffer.add_string sb "Watched Assets:\n";
      List.iter
	(fun alpha ->
	  match Ctre.ctree_addr alpha ctr with
	  | (Some(Ctre.CLeaf(_,hl)),_) ->
	      Buffer.add_string sb (Cryptocurr.addr_qedaddrstr alpha);
	      Buffer.add_string sb ":\n";
	      Ctre.print_hlist_to_buffer sb 0L (Ctre.nehlist_hlist hl)
	  | (None,_) ->
	      Buffer.add_string sb (Cryptocurr.addr_qedaddrstr alpha);
	      Buffer.add_string sb ": empty\n";
	  | _ ->
	      Buffer.add_string sb (Cryptocurr.addr_qedaddrstr alpha);
	      Buffer.add_string sb ": no information\n";
	  )
	!walletwatchaddrs;
      send_string c (Buffer.contents sb)
  | ImportWatchAddr(a) ->
      begin
	try
	  let alpha = Cryptocurr.qedaddrstr_addr a in
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
	  let (k,b) = Cryptocurr.privkey_from_wif w in
	  match Secp256k1.smulp k Secp256k1._g with
	  | Some(x,y) ->
	      let h = Cryptocurr.pubkey_hashval (x,y) b in
	      let alpha = Cryptocurr.addr_qedaddrstr (Hash.hashval_p2pkh_addr h) in
	      walletkeys := (k,b,(x,y),Cryptocurr.qedwif k b,h,alpha)::!walletkeys;
	      write_wallet();
	      output_byte c 1;
	      send_string c alpha
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
  | _ -> ()

