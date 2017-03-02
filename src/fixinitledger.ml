(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int;;
open Utils;;
open Ser;;
open Sha256;;
open Hash;;
open Ser;;
open Net;;
open Db;;
open Secp256k1;;
open Signat;;
open Cryptocurr;;
open Mathdata;;
open Assets;;
open Tx;;
open Ctre;;
open Ctregraft;;
open Block;;
open Blocktree;;
open Setconfig;;

let exitfn : (int -> unit) ref = ref (fun n -> exit n);;

let lock datadir =
  let lf = Filename.concat datadir ".lock" in
  let c = open_out lf in
  close_out c;
  exitfn := (fun n -> saveknownpeers(); Sys.remove lf; exit n);;

let print_index d =
  let dind = Filename.concat d "index" in
  if Sys.file_exists dind then
    let ch = open_in_bin dind in
    let c = ref (ch, None) in
    begin
      try
	while true do
	  let (h, c2) = sei_hashval seic !c in
	  let (p, c2) = sei_int32 seic !c in
    let a = DbAssetH.dbget h in
    let ha = hashasset a in
    Printf.printf "Put hash and asset\n";
    DbAssetIDH.dbput h ha;
    DbAsset.dbput ha a;
    Printf.printf "%s  --- %s\n" (hashval_hexstring h) (hashval_hexstring ha);
	  c := c2
	done
      with
      | End_of_file -> close_in ch
      | exc -> close_in ch; raise exc
    end
  else
    ()

let rec traverse_a d =
      if Sys.file_exists d && Sys.is_directory d then
	begin
	  List.iter
	    (fun h ->
	      traverse_a (Filename.concat d h))
	    ["00";"01";"02";"03";"04";"05";"06";"07";"08";"09";"0a";"0b";"0c";"0d";"0e";"0f";"10";"11";"12";"13";"14";"15";"16";"17";"18";"19";"1a";"1b";"1c";"1d";"1e";"1f";"20";"21";"22";"23";"24";"25";"26";"27";"28";"29";"2a";"2b";"2c";"2d";"2e";"2f";"30";"31";"32";"33";"34";"35";"36";"37";"38";"39";"3a";"3b";"3c";"3d";"3e";"3f";"40";"41";"42";"43";"44";"45";"46";"47";"48";"49";"4a";"4b";"4c";"4d";"4e";"4f";"50";"51";"52";"53";"54";"55";"56";"57";"58";"59";"5a";"5b";"5c";"5d";"5e";"5f";"60";"61";"62";"63";"64";"65";"66";"67";"68";"69";"6a";"6b";"6c";"6d";"6e";"6f";"70";"71";"72";"73";"74";"75";"76";"77";"78";"79";"7a";"7b";"7c";"7d";"7e";"7f";"80";"81";"82";"83";"84";"85";"86";"87";"88";"89";"8a";"8b";"8c";"8d";"8e";"8f";"90";"91";"92";"93";"94";"95";"96";"97";"98";"99";"9a";"9b";"9c";"9d";"9e";"9f";"a0";"a1";"a2";"a3";"a4";"a5";"a6";"a7";"a8";"a9";"aa";"ab";"ac";"ad";"ae";"af";"b0";"b1";"b2";"b3";"b4";"b5";"b6";"b7";"b8";"b9";"ba";"bb";"bc";"bd";"be";"bf";"c0";"c1";"c2";"c3";"c4";"c5";"c6";"c7";"c8";"c9";"ca";"cb";"cc";"cd";"ce";"cf";"d0";"d1";"d2";"d3";"d4";"d5";"d6";"d7";"d8";"d9";"da";"db";"dc";"dd";"de";"df";"e0";"e1";"e2";"e3";"e4";"e5";"e6";"e7";"e8";"e9";"ea";"eb";"ec";"ed";"ee";"ef";"f0";"f1";"f2";"f3";"f4";"f5";"f6";"f7";"f8";"f9";"fa";"fb";"fc";"fd";"fe";"ff"];
    print_index d
	end

let traverse_asseth dbdir =
  traverse_a (Filename.concat dbdir "asseth")


let load_hlist_element h =
  match DbHConsEltH.dbget h with
  | (ah, Some(k)) -> HConsH(ah, HHash(k))
  | (ah, None) -> HConsH(ah, HNil)

let load_nehlist_element h =
  match DbHConsEltH.dbget h with
  | (ah, Some(k)) -> NehConsH(ah, HHash(k))
  | (ah, None) -> NehConsH(ah, HNil)


let rec repair_hlist hl =
  match hl with
  | HNil -> None
  | HHash(r) -> repair_hlist (load_hlist_element r)
  | HCons(a, hr) ->
    let ah = DbAssetIDH.dbget (assetid a) in
    let h = repair_hlist hr in
    let r = match h with
      | None -> hashtag ah 3l
      | Some(k) -> hashtag (hashpair ah k) 4l
    in
    DbHConsElt.dbput r (ah, h);
    Some(r)
  | HConsH(a, hr) ->
    let ah = DbAssetIDH.dbget a in
    let h = repair_hlist hr in
    let r = match h with
      | None -> hashtag ah 3l
      | Some(k) -> hashtag (hashpair ah k) 4l
    in
    DbHConsElt.dbput r (ah, h);
    Some(r)


let rec repair_nehlist hl =
  match hl with
  | NehHash(r) -> repair_nehlist (load_nehlist_element r)
  | NehCons(a, hr) ->
    let ah = DbAssetIDH.dbget (assetid a) in
    let h = repair_hlist hr in
    let r = match h with
      | None -> hashtag ah 3l
      | Some(k) -> hashtag (hashpair ah k) 4l
    in
    DbHConsElt.dbput r (ah, h);
    r
  | NehConsH(a, hr) ->
    let ah = DbAssetIDH.dbget a in
    let h = repair_hlist hr in
    let r = match h with
      | None -> hashtag ah 3l
      | Some(k) -> hashtag (hashpair ah k) 4l
    in
    DbHConsElt.dbput r (ah, h);
    r

let rec repair_ctree c =
  match c with
  | CLeaf(bl, hl) -> CLeaf(bl, NehHash(repair_nehlist hl))
  | CHash(h) -> CHash(save_ctree_elements (repair_ctree (DbCTreeEltH.dbget h)))
  | CLeft(c0) -> CLeft(repair_ctree c0)
  | CRight(c1) -> CRight(repair_ctree c1)
  | CBin(c0,c1) -> CBin(repair_ctree c0, repair_ctree c1)

let save_repaired c = save_ctree_elements (repair_ctree c)

let traverse () =
  Printf.printf "ctree\n";
  let f k = Printf.printf "-- %s\n" (hashval_hexstring k); save_repaired (DbCTreeEltH.dbget k); () in
  DbCTreeEltH.dbkeyiter f
;;

datadir_from_command_line(); (*** if -datadir=... is on the command line, then set Config.datadir so we can find the config file ***)
process_config_file();
process_config_args(); (*** settings on the command line shadow those in the config file ***)

if not !Config.testnet then (Printf.printf "Qeditas can only be run on testnet for now. Please give the -testnet command line argument.\n"; exit 1);
begin
  match !Config.checkpointskey with
    None -> ()
  | Some(w) ->
    let (k,b) = privkey_from_wif w in
    match smulp k Secp256k1._g with
    | Some(x,y) ->
      if not b && eq_big_int x checkpointspubkeyx && eq_big_int y checkpointspubkeyy then
        checkpointsprivkeyk := Some(k)
      else
        raise (Failure "Incorrect testnet checkpointskey given")
    | None ->
      raise (Failure "Incorrect testnet checkpointskey given")
end;

let datadir = if !Config.testnet then (Filename.concat !Config.datadir "testnet") else !Config.datadir in
if Sys.file_exists (Filename.concat datadir ".lock") then
  begin
    Printf.printf "Cannot start Qeditas. Do you already have Qeditas running? If not, remove: %s\n" (Filename.concat datadir ".lock");
    flush stdout;
    exit 1;
  end;

lock datadir;
let dbdir = Filename.concat datadir "db" in
let old_ctr = CHash(hexstring_hashval "66c029f4c29b351785c0480cedc9449b64332dfa") in
dbconfig dbdir;
Printf.printf "Initialize...\n"; flush stdout;
DbAsset.dbinit();
DbAssetH.dbinit();
DbAssetIDH.dbinit();
DbHConsElt.dbinit();
DbCTreeElt.dbinit();
DbHConsEltH.dbinit();
DbCTreeEltH.dbinit();
Printf.printf "Fix assets...\n"; flush stdout;
traverse_asseth dbdir;
Printf.printf "Fix ctrees and hlist...\n"; flush stdout;
let tr = repair_ctree old_ctr in
save_ctree_elements tr;
print_ctree tr;
flush stdout
