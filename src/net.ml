(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Ser
open Hashaux
open Hash
open Assets
open Signat
open Tx
open Ctre
open Block

let stxpool : (hashval,stx) Hashtbl.t = Hashtbl.create 1000;;
let published_stx : (hashval,unit) Hashtbl.t = Hashtbl.create 1000;;
let thytree : (hashval,Mathdata.ttree) Hashtbl.t = Hashtbl.create 1000;;
let sigtree : (hashval,Mathdata.stree) Hashtbl.t = Hashtbl.create 1000;;

type blocktree = BlocktreeNode of blocktree option * hashval list ref * hashval option * hashval option * hashval option * hashval * targetinfo * int32 * int64 * big_int * int64 * bool option ref * bool ref * (hashval * blocktree) list ref

let genesistimestamp = 1452875010L;;
let genesisblocktreenode = BlocktreeNode(None,ref [],None,None,None,!genesisledgerroot,(!genesiscurrentstakemod,!genesisfuturestakemod,!genesistarget),600l,genesistimestamp,zero_big_int,1L,ref (Some(true)),ref false,ref []);;

let lastcheckpointnode = ref genesisblocktreenode;;

let bestnode = ref genesisblocktreenode;;

let eq_node n1 n2 =
  let BlocktreeNode(_,_,pbh1,_,_,_,_,_,_,_,_,_,_,_) = n1 in
  let BlocktreeNode(_,_,pbh2,_,_,_,_,_,_,_,_,_,_,_) = n2 in
  pbh1 = pbh2

let blkheadernode : (hashval option,blocktree) Hashtbl.t = Hashtbl.create 1000;;
Hashtbl.add blkheadernode None genesisblocktreenode;;
let orphanblkheaders : (hashval option,blockheader) Hashtbl.t = Hashtbl.create 1000;;
let earlyblocktreenodes : (int64 * blocktree) list ref = ref [];;
let tovalidatelist : (bool option ref * (unit -> unit)) list ref = ref [];;

let known_thytree_p thyroot =
  match thyroot with
  | None -> true
  | Some(r) -> Hashtbl.mem thytree r

let known_sigtree_p sigroot =
  match sigroot with
  | None -> true
  | Some(r) -> Hashtbl.mem sigtree r

let lookup_thytree thyroot =
  match thyroot with
  | None -> None
  | Some(r) -> Some(Hashtbl.find thytree r)

let lookup_sigtree sigroot =
  match sigroot with
  | None -> None
  | Some(r) -> Some(Hashtbl.find sigtree r)

let add_thytree thyroot otht =
  match thyroot,otht with
  | Some(r),Some(tht) -> if not (Hashtbl.mem thytree r) then Hashtbl.add thytree r tht
  | _,_ -> ()

let add_sigtree sigroot osigt =
  match sigroot,osigt with
  | Some(r),Some(sigt) -> if not (Hashtbl.mem sigtree r) then Hashtbl.add sigtree r sigt
  | _,_ -> ()

let rec insertnewdelayed (tm,n) btnl =
  match btnl with
  | [] -> [(tm,n)]
  | (tm2,n2)::btnr when tm < tm2 -> (tm,n)::btnl
  | (tm2,n2)::btnr -> (tm2,n2)::insertnewdelayed (tm,n) btnr

exception Hung

let sethungsignalhandler () =
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Hung));;

let input_byte_nohang c tm =
  try
    ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = tm });
    let b = input_byte c in
    try
      ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = 0.0 });
      Some(b)
    with Hung -> (** in case the alarm is signaled after the connection was accepted but before the function returned, catch Hung and continue **)
      Some(b)
  with
  | Hung -> None
  | exc -> (** if it's another exception make sure to disable the timer **)
      ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = 0.0 });
      raise exc

let process_new_tx h =
  Printf.printf "Processing new tx %s\n" h; flush stdout;
  let qednetch = Unix.open_process_in ((qednetd()) ^ " loaddata qtx " ^ h) in
  let txhd = input_line qednetch in
  ignore (Unix.close_process_in qednetch);
  try
    let s = hexstring_string txhd in
    let (stx1,_) = sei_stx seis (s,String.length s,None,0,0) in
    let (tx1,_) = stx1 in
    let txid = hashtx tx1 in
    if not (txid = hexstring_hashval h) then (*** wrong hash, remove it but don't blacklist the (wrong) hashval ***)
      begin
        Printf.printf "WARNING: Received tx with different hash as advertised, removing %s\nThis may e due to a bug or due to a misbehaving peer.\n" h; flush stdout;
        let qednetch = Unix.open_process_in ((qednetd()) ^ " removedata qtx " ^ h) in
        ignore (Unix.close_process_in qednetch)
      end
    else if tx_valid tx1 then
      begin (*** checking the validity of signatures and support depend on the current ledger; delay this here in favor of checking them before including them in a block we're actively trying to stake; note that the relevant properties are checked when they are included in a block as part of checking a block is valid ***)
        Hashtbl.add stxpool txid stx1;
     end
   else
   (*** in this case, reject the tx since it's definitely not valid ***)
     begin
       let qednetch = Unix.open_process_in ((qednetd()) ^ " blacklistdata qtx " ^ h) in
       ignore (Unix.close_process_in qednetch);
       let qednetch = Unix.open_process_in ((qednetd()) ^ " removedata qtx " ^ h) in
       ignore (Unix.close_process_in qednetch)
     end
  with (*** in some cases, failure should lead to blacklist and removal of the tx, but it's not clear which cases; if it's in a block we might need to distinguish between definitely incorrect vs. possibly incorrect ***)
  | Not_found ->
    Printf.printf "Problem with tx, deleting it\n"; flush stdout;
    let qednetch = Unix.open_process_in ((qednetd()) ^ " removedata qtx " ^ h) in
    ignore (Unix.close_process_in qednetch)
  | e ->
    Printf.printf "exception %s\n" (Printexc.to_string e); flush stdout;
    ()

let rec processdelayednodes tm btnl =
  match btnl with
  | (tm2,n2)::btnr when tm2 <= tm ->
    let BlocktreeNode(_,_,_,_,_,_,_,_,_,bestcumulstk,_,_,_,_) = !bestnode in
    let BlocktreeNode(_,_,pbh,_,_,_,_,_,_,newcumulstk,_,_,_,_) = n2 in
    if gt_big_int newcumulstk bestcumulstk then
      begin
        Printf.printf "New best blockheader %s\n" (match pbh with Some(h) -> hashval_hexstring h | None -> "(genesis)"); flush stdout;
        bestnode := n2
      end;
    processdelayednodes tm btnr
  | _ -> btnl

let rec processblockvalidation vl =
  match vl with
  | [] -> []
  | (v,f)::vr ->
      let vr2 = processblockvalidation vr in
      f();
      match !v with
      | Some(_) -> vr2
      | None -> (v,f)::vr2

let add_to_headers_file h =
  let fn = Filename.concat (datadir()) "headers" in
  let f = open_out_gen [Open_append;Open_creat] 0o440 fn in
  output_string f (h ^ "\n");
  close_out f

let rec is_recent_staker stkaddr n i =
  if i > 0 then
    begin
      let BlocktreeNode(par,stakers,_,_,_,_,_,_,_,_,_,_,_,_) = n in
      if List.mem stkaddr !stakers then
	true
      else
	match par with
	| Some(p) -> is_recent_staker stkaddr p (i-1)
	| _ -> false
    end
  else
    false

let rec record_recent_staker stkaddr n i =
  if i > 0 then
    begin
      let BlocktreeNode(par,stakers,_,_,_,_,_,_,_,_,_,_,_,_) = n in
      stakers := stkaddr::!stakers;
      match par with
      | Some(p) -> record_recent_staker stkaddr p (i-1)
      | None -> ()
    end

let rec process_new_header_a h hh blkh1 blkhd1 initialization =
  let prevblkh = blkhd1.prevblockhash in
  begin
    try
      let prevnode = Hashtbl.find blkheadernode prevblkh in
      let BlocktreeNode(_,_,_,thyroot,sigroot,ledgerroot,tinfo,deltm,tmstamp,prevcumulstk,blkhght,validated,blacklisted,succl) = prevnode in
      if !blacklisted then (*** child of a blacklisted node, drop and blacklist it ***)
        begin
          let qednetch = Unix.open_process_in ((qednetd()) ^ " blacklistdata qblockheader " ^ h) in
          ignore (Unix.close_process_in qednetch);
          let qednetch = Unix.open_process_in ((qednetd()) ^ " removedata qblockheader " ^ h) in
          ignore (Unix.close_process_in qednetch)
        end
      else if valid_blockheader blkhght blkh1 && blockheader_succ_a deltm tmstamp tinfo blkh1 then
        let (_,_,tar1) = blkhd1.tinfo in
        let newcumulstake = cumul_stake prevcumulstk tar1 blkhd1.deltatime in
	let validated = ref None in
        let newnode = BlocktreeNode(Some(prevnode),ref [blkhd1.stakeaddr],prevblkh,blkhd1.newtheoryroot,blkhd1.newsignaroot,blkhd1.newledgerroot,blkhd1.tinfo,blkhd1.deltatime,blkhd1.timestamp,newcumulstake,Int64.add blkhght 1L,validated,ref false,ref []) in
        begin (*** add it as a leaf, indicate that we want the block delta to validate it, and check if it's the best ***)
          succl := (hh,newnode)::!succl;
	  record_recent_staker blkhd1.stakeaddr prevnode 6;
	  let validatefn () =
	    try
	      let qednetch = Unix.open_process_in ((qednetd()) ^ " loaddata qblockdeltah " ^ h) in
	      let blkdhh = input_line qednetch in
	      ignore (Unix.close_process_in qednetch);
	      let blkdhs = hexstring_string blkdhh in
	      let (blkdh,_) = sei_blockdeltah seis (blkdhs,String.length blkdhs,None,0,0) in
	      let (stkout,forf,cg,txhl) = blkdh in
	      let alltxs = ref true in
	      List.iter
		(fun txh ->
		  if not (Hashtbl.mem stxpool txh) then
		    begin
		      alltxs := false;
		      let qednetch = Unix.open_process_in ((qednetd()) ^ " getdata qtx " ^ (hashval_hexstring txh)) in
		      ignore (Unix.close_process_in qednetch);
		    end)
		txhl;
	      if !alltxs then
		let blkdel = { stakeoutput = stkout;
			       forfeiture = forf;
			       prevledgergraft = cg;
			       blockdelta_stxl = List.map (fun txh -> Hashtbl.find stxpool txh) txhl
			     }
		in
		let blk = (blkh1,blkdel) in
		if known_thytree_p thyroot && known_sigtree_p sigroot then (*** these should both be known if the parent block has been validated ***)
		  if valid_block (lookup_thytree thyroot) (lookup_sigtree sigroot) blkhght blk then
		    begin (*** if valid_block succeeds, then latesttht and latestsigt will be set to the transformed theory tree and signature tree ***)
		      validated := Some(true);
		      add_thytree blkhd1.newtheoryroot !latesttht;
		      add_sigtree blkhd1.newsignaroot !latestsigt;
		    end
		  else
		    begin
		      validated := Some(false); (*** could delete and possibly blacklist the qblockdeltah, but will leave it for now ***)
		    end
	    with
	    | End_of_file ->
	      let qednetch = Unix.open_process_in ((qednetd()) ^ " getdata qblockdeltah " ^ h) in
	      ignore (Unix.close_process_in qednetch);
	  in
	  tovalidatelist := (validated,validatefn)::!tovalidatelist;
          if not initialization then add_to_headers_file h;
          if Int64.of_float (Unix.time()) < tmstamp then (*** delay it ***)
            earlyblocktreenodes := insertnewdelayed (tmstamp,newnode) !earlyblocktreenodes
          else
            let BlocktreeNode(_,_,_,_,_,_,_,_,_,bestcumulstk,_,_,_,_) = !bestnode in
            if gt_big_int newcumulstake bestcumulstk then
              begin
                Printf.printf "New best blockheader %s\n" h; flush stdout;
                bestnode := newnode
              end;
          List.iter
            (fun blkh1 -> let (blkhd1,_) = blkh1 in let hh = hash_blockheaderdata blkhd1 in process_new_header_a (hashval_hexstring hh) hh blkh1 blkhd1 initialization)
            (Hashtbl.find_all orphanblkheaders (Some(hh)))
        end
      else
        begin (*** if it's wrong, delete it and blacklist it so it won't look new in the future ***)
          Printf.printf "Incorrect blockheader, deleting and blacklisting\n"; flush stdout;
          let qednetch = Unix.open_process_in ((qednetd()) ^ " blacklistdata qblockheader " ^ h) in
          ignore (Unix.close_process_in qednetch);
          let qednetch = Unix.open_process_in ((qednetd()) ^ " removedata qblockheader " ^ h) in
          ignore (Unix.close_process_in qednetch)
        end
    with Not_found -> (*** orphan block header, put it on the relevant hash table and request parent ***)
      Hashtbl.add orphanblkheaders prevblkh blkh1;
      match prevblkh with
      | Some(pbh) ->
        let qednetch = Unix.open_process_in ((qednetd()) ^ " getdata qblockheader " ^ (hashval_hexstring pbh)) in
        let l = input_line qednetch in
        if l = "already have" then process_new_header (hashval_hexstring pbh) initialization;
        ignore (Unix.close_process_in qednetch);
      | None -> ()
  end
and process_new_header h initialization =
  Printf.printf "Processing new header %s\n" h; flush stdout;
  let qednetch = Unix.open_process_in ((qednetd()) ^ " loaddata qblockheader " ^ h) in
  let blkhd = input_line qednetch in
  ignore (Unix.close_process_in qednetch);
  try
    let s = hexstring_string blkhd in
    let (blkh1,_) = sei_blockheader seis (s,String.length s,None,0,0) in
    let (blkhd1,blkhs1) = blkh1 in
    let hh = hexstring_hashval h in
    if not (hash_blockheaderdata blkhd1 = hh) then (*** wrong hash, remove it but don't blacklist the (wrong) hashval ***)
      begin
        Printf.printf "WARNING: Received block header with different hash as advertised, removing %s\nThis may e due to a bug or due to a misbehaving peer.\n" h; flush stdout;
        let qednetch = Unix.open_process_in ((qednetd()) ^ " removedata qblockheader " ^ h) in
        ignore (Unix.close_process_in qednetch)
      end
    else
      process_new_header_a h hh blkh1 blkhd1 initialization
  with (*** in some cases, failure should lead to blacklist and removal of the tx, but it's not clear which cases; if it's in a block we might need to distinguish between definitely incorrect vs. possibly incorrect ***)
  | Not_found ->
    Printf.printf "Problem with blockheader, deleting it\n"; flush stdout;
    let qednetch = Unix.open_process_in ((qednetd()) ^ " removedata qblockheader " ^ h) in
    ignore (Unix.close_process_in qednetch)
  | e ->
    Printf.printf "exception %s\n" (Printexc.to_string e); flush stdout;
    ()

let init_headers () =
  let fn = Filename.concat (datadir()) "headers" in
  if Sys.file_exists fn then
    let f = open_in fn in
    begin
      try
        let h = input_line f in
        process_new_header h true
      with End_of_file -> close_in f
    end
  else
    ()

let rec find_best_validated_block_from fromnode bestcumulstk =
  let BlocktreeNode(_,_,_,_,_,_,_,_,_,cumulstk,_,validatedp,blklistp,succl) = fromnode in
  if not !blklistp && !validatedp = Some(true) then
    begin
      let newbestcumulstk = ref
	(if gt_big_int cumulstk bestcumulstk then
	  begin
	    bestnode := fromnode;
	    cumulstk
	  end
	else
	  bestcumulstk)
      in
      List.iter
	(fun (_,childnode) ->
	  newbestcumulstk := find_best_validated_block_from childnode !newbestcumulstk)
	!succl;
      !newbestcumulstk
    end
  else
    bestcumulstk

let publish_stx txh stx1 =
  let txhh = hashval_hexstring txh in
  let fn = Filename.concat (datadir()) ("t" ^ txhh) in
  let ch = open_out_gen [Open_wronly;Open_binary;Open_creat] 0o644 fn in
  let c = seo_stx seoc stx1 (ch,None) in
  seocf c;
  close_out ch;
  let qednetch = Unix.open_process_in ((qednetd()) ^ " adddatafromfile qtx " ^ txhh ^ " " ^ fn) in
  ignore (Unix.close_process_in qednetch);
  Sys.remove fn;
  Hashtbl.add published_stx txh ()

let publish_block bhh (bh,bd) =
  let bhhh = hashval_hexstring bhh in
  let fn = Filename.concat (datadir()) ("h" ^ bhhh) in
  let ch = open_out_gen [Open_wronly;Open_binary;Open_creat] 0o644 fn in
  let c = seo_blockheader seoc bh (ch,None) in
  seocf c;
  close_out ch;
  let qednetch = Unix.open_process_in ((qednetd()) ^ " adddatafromfile qblockheader " ^ bhhh ^ " " ^ fn) in
  ignore (Unix.close_process_in qednetch);
  Sys.remove fn;
  let stxhl =
    List.map
      (fun (tx1,txsg1) ->
	let tx1h = hashtx tx1 in
	if not (Hashtbl.mem published_stx tx1h) then publish_stx tx1h (tx1,txsg1);
	tx1h)
      bd.blockdelta_stxl
  in
  let bdh = (bd.stakeoutput,bd.forfeiture,bd.prevledgergraft,stxhl) in
  let fn = Filename.concat (datadir()) ("d" ^ bhhh) in
  let ch = open_out_gen [Open_wronly;Open_binary;Open_creat] 0o644 fn in
  let c = seo_blockdeltah seoc bdh (ch,None) in
  seocf c;
  close_out ch;
  let qednetch = Unix.open_process_in ((qednetd()) ^ " adddatafromfile qblockdeltah " ^ bhhh ^ " " ^ fn) in
  ignore (Unix.close_process_in qednetch);
  Sys.remove fn

let qednetmain initfn preloopfn =
  sethungsignalhandler();
  Printf.printf "Starting qednetd\n"; flush stdout;
  let (qednetch1,qednetch2,qednetch3) = Unix.open_process_full (qednetd()) (Unix.environment()) in
  Printf.printf "Init headers\n"; flush stdout;
  init_headers();
  initfn();
  Printf.printf "Initialization phase complete.\n"; flush stdout;
  while true do
    try
      preloopfn();
      earlyblocktreenodes := processdelayednodes (Int64.of_float (Unix.time())) !earlyblocktreenodes;
      tovalidatelist := processblockvalidation !tovalidatelist;
      ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = 1.0 });
      let l = input_line qednetch3 in
      ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = 0.0 });
      let ll = String.length l in
      if ll = 68 && String.sub l 0 4 = "QTX:" then
	process_new_tx (String.sub l 28 40)
      else if ll = 72 && String.sub l 0 8 = "QHEADER:" then
	process_new_header (String.sub l 32 40) false
    with Hung -> ()
  done

