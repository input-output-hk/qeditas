open Ser
open Hash

let max_in_cache = 128
let max_entries_in_dir = 65536
let stop_after_byte = 100000000
let defrag_limit = 1024
let dbdir = ref ""

let dbconfig dir =
  dbdir := dir;
  if Sys.file_exists dir then
    if Sys.is_directory dir then
      ()
    else
      raise (Failure (dir ^ " is a file not a directory"))
  else
    begin
      Unix.mkdir dir 0b111111000
    end

let load_index d =
  let dind = Filename.concat d "index" in
  if Sys.file_exists dind then
    let ch = open_in_bin dind in
    let c = ref (ch,None) in
    let r = ref [] in
    begin
      try
	while true do
	  let (h,c2) = sei_hashval seic !c in
	  let (p,c2) = sei_int32 seic !c in
	  r := (h,Int32.to_int p)::!r;
	  c := c2
	done;
	[]
      with
      | End_of_file ->
	  close_in ch;
	  !r
      | exc ->
	  close_in ch;
	  raise exc
    end
  else
    []

let load_index_to_hashtable ht d =
  let dind = Filename.concat d "index" in
  if Sys.file_exists dind then
    let ch = open_in_bin dind in
    let c = ref (ch,None) in
    begin
      try
	while true do
	  let (h,c2) = sei_hashval seic !c in
	  let (p,c2) = sei_int32 seic !c in
	  Hashtbl.add ht h (d,Int32.to_int p);
	  c := c2
	done
      with
      | End_of_file ->
	  close_in ch
      | exc ->
	  close_in ch;
	  raise exc
    end
  else
    ()

let count_index d =
  let dind = Filename.concat d "index" in
  if Sys.file_exists dind then
    let ch = open_in_bin dind in
    let i = (in_channel_length ch) / 24 in
    close_in ch;
    i
  else
    0

let find_in_index d k =
  let dind = Filename.concat d "index" in
  if Sys.file_exists dind then
    let ch = open_in_bin dind in
    let l = in_channel_length ch in
    let b = ref 0 in
    let e = ref (l / 24) in
    let r = ref None in
    begin
      try
	while !r = None do
	  if !b < !e then
	    let m = !b + (!e - !b) / 2 in
	    begin
	      seek_in ch (m*24);
	      let (h,c2) = sei_hashval seic (ch,None) in
	      let chk = compare h k in
	      if chk = 0 then
		let (p,c2) = sei_int32 seic c2 in r := Some(Int32.to_int p)
	      else if chk > 0 then
		e := m
	      else
		b := m+1
	    end
	  else
	    raise End_of_file
	done;
	close_in ch;
	match !r with
	| Some(p) -> p
	| None -> raise Not_found
      with
      | End_of_file ->
	  close_in ch;
	  raise Not_found
      | exc ->
	  close_in ch;
	  raise exc
    end
  else
    raise Not_found

let count_deleted d =
  let ddel = Filename.concat d "deleted" in
  if Sys.file_exists ddel then
    let ch = open_in_bin ddel in
    let i = (in_channel_length ch) / 20 in
    close_in ch;
    i
  else
    0

let find_in_deleted d k =
  let ddel = Filename.concat d "deleted" in
  if Sys.file_exists ddel then
    let ch = open_in_bin ddel in
    let c = ref (ch,None) in
    let r = ref false in
    begin
      try
	while not !r do
	  let (h,c2) = sei_hashval seic !c in
	  if h = k then r := true;
	  c := c2
	done;
	close_in ch;
	()
      with
      | End_of_file ->
	  close_in ch;
	  raise Not_found
      | exc ->
	  close_in ch;
	  raise exc
    end
  else
    raise Not_found

let load_deleted d =
  let ddel = Filename.concat d "deleted" in
  if Sys.file_exists ddel then
    let ch = open_in_bin ddel in
    let c = ref (ch,None) in
    let r = ref [] in
    begin
      try
	while true do
	  let (h,c2) = sei_hashval seic !c in
	  r := h::!r;
	  c := c2
	done;
	[]
      with
      | End_of_file ->
	close_in ch;
	!r
      | exc ->
	  close_in ch;
	  raise exc
    end
  else
    []

let load_deleted_to_hashtable ht d =
  let ddel = Filename.concat d "deleted" in
  if Sys.file_exists ddel then
    let ch = open_in_bin ddel in
    let c = ref (ch,None) in
    begin
      try
	while true do
	  let (h,c2) = sei_hashval seic !c in
	  Hashtbl.add ht h ();
	  c := c2
	done
      with
      | End_of_file ->
	  close_in ch
      | exc ->
	  close_in ch;
	  raise exc
    end
  else
    ()

let undelete d k =
  let dl = load_deleted d in
  let ddel = Filename.concat d "deleted" in
  let chd = open_out_gen [Open_wronly;Open_trunc;Open_binary] 0b110110000 ddel in
  try
    List.iter
      (fun h ->
	if not (h = k) then
	  let cd2 = seo_hashval seoc h (chd,None) in
	  seocf cd2)
      dl;
    close_out chd
  with exc ->
    close_out chd;
    raise exc

let rec dbfind_a d i k kh =
  try
    let p = find_in_index d k in
    (d,p)
  with Not_found ->
    if i < 20 then
      let dk' = Filename.concat d (String.sub kh i 2) in
      try
	if Sys.is_directory dk' then
	  dbfind_a dk' (i+2) k kh
	else
	  raise Not_found
      with _ -> raise Not_found
    else
      raise Not_found

let dbfind d k =
  let fd = Filename.concat !dbdir d in
  try
    if Sys.is_directory fd then
      dbfind_a fd 0 k (hashval_hexstring k)
    else
      raise (Failure (fd ^ " is a file not a directory"))
  with _ -> raise Not_found

let file_length f =
  if Sys.file_exists f then
    let ch = open_in_bin f in
    let l = in_channel_length ch in
    close_in ch;
    l
  else
    0

let rec dbfind_next_space_a d i k =
  if count_index d < max_entries_in_dir then
    let dd = Filename.concat d "data" in
    let p = file_length dd in
    if p < stop_after_byte then
      (d,p)
    else
      dbfind_next_space_b d i k
  else
    dbfind_next_space_b d i k
and dbfind_next_space_b d i k =
  let dk' = Filename.concat d (String.sub k i 2) in
  if Sys.file_exists dk' then
    if Sys.is_directory dk' then
      dbfind_next_space_a dk' (i+2) k
    else
      raise (Failure (dk' ^ " is a file not a directory"))
  else
    begin
      Unix.mkdir dk' 0b111111000;
      (dk',0)
    end

let dbfind_next_space d k =
  let fd = Filename.concat !dbdir d in
  if Sys.file_exists fd then
    if Sys.is_directory fd then
      dbfind_next_space_a fd 0 (hashval_hexstring k)
    else
      raise (Failure (fd ^ " is a file not a directory"))
  else
    begin
      Unix.mkdir fd 0b111111000;
      (fd,0)
    end

let defrag d seival seoval =
  let ind = ref (load_index d) in
  let indf = Filename.concat d "index" in
  let datf = Filename.concat d "data" in
  let del = load_deleted d in
  let chd = open_in_bin datf in
  let l = in_channel_length chd in
  let dat =
    ref (List.map
	   (fun (k,p) ->
	     if List.mem k del then
	       None
	     else if p < l then
	       begin
		 seek_in chd p;
		 let (v,_) = seival (chd,None) in
		 Some(v)
	       end
	     else
	       begin
		 close_in chd;
		 raise (Failure ("Corrupted data file " ^ datf))
	       end)
	   !ind)
  in
  close_in chd;
  Sys.remove (Filename.concat d "deleted");
  let chd = open_out_gen [Open_wronly;Open_trunc;Open_binary] 0b110110000 datf in
  let newind = ref [] in
  try
    while not (!ind = []) do
      match (!ind,!dat) with
      | ((k,_)::ir,Some(v)::dr) ->
	  ind := ir;
	  dat := dr;
	  if not (List.mem k del) then
	    let p = pos_out chd in
	    newind := List.merge (fun (h',p') (k',q') -> compare h' k') !newind [(k,p)];
	    let cd2 = seoval v (chd,None) in
	    seocf cd2;
      | ((k,_)::ir,None::dr) ->
	  ind := ir;
	  dat := dr
      | _ ->
	  raise (Failure ("impossible"))
    done;
    let chi = open_out_gen [Open_wronly;Open_trunc;Open_binary] 0b110110000 indf in
    begin
      try
	List.iter (fun (k,p) ->
	  let ci2 = seo_hashval seoc k (chi,None) in
	  let ci2 = seo_int32 seoc (Int32.of_int p) ci2 in
	  seocf ci2)
	  !newind;
	close_out chi;
	close_out chd
      with exc ->
	close_out chi;
	raise exc
    end
  with exc ->
    close_out chd;
    raise exc

module type dbtype = functor (M:sig type t val basedir : string val seival : (seict -> t * seict) val seoval : (t -> seoct -> seoct) end) ->
  sig
    val dbinit : unit -> unit
    val dbget : hashval -> M.t
    val dbexists : hashval -> bool
    val dbput : hashval -> M.t -> unit
    val dbdelete : hashval -> unit
  end

module type dbtypekeyiter = functor (M:sig type t val basedir : string val seival : (seict -> t * seict) val seoval : (t -> seoct -> seoct) end) ->
  sig
    val dbinit : unit -> unit
    val dbget : hashval -> M.t
    val dbexists : hashval -> bool
    val dbput : hashval -> M.t -> unit
    val dbdelete : hashval -> unit
    val dbkeyiter : (hashval -> unit) -> unit
  end

module Dbbasic2 : dbtype = functor (M:sig type t val basedir : string val seival : (seict -> t * seict) val seoval : (t -> seoct -> seoct) end) ->
  struct
    let mutexdb : Mutex.t = Mutex.create()

    let withlock f =
      try
	Mutex.lock mutexdb;
	let r = f() in
	Mutex.unlock mutexdb;
	r
      with e ->
	Mutex.unlock mutexdb;
	raise e

    let indextable : (hashval,(string * int)) Hashtbl.t = Hashtbl.create 10000
    let deletedtable : (hashval,unit) Hashtbl.t = Hashtbl.create 100

    let rec dbinit_a d =
      if Sys.file_exists d && Sys.is_directory d then
	begin
	  List.iter
	    (fun h ->
	      dbinit_a (Filename.concat d h))
	    ["00";"01";"02";"03";"04";"05";"06";"07";"08";"09";"0a";"0b";"0c";"0d";"0e";"0f";"10";"11";"12";"13";"14";"15";"16";"17";"18";"19";"1a";"1b";"1c";"1d";"1e";"1f";"20";"21";"22";"23";"24";"25";"26";"27";"28";"29";"2a";"2b";"2c";"2d";"2e";"2f";"30";"31";"32";"33";"34";"35";"36";"37";"38";"39";"3a";"3b";"3c";"3d";"3e";"3f";"40";"41";"42";"43";"44";"45";"46";"47";"48";"49";"4a";"4b";"4c";"4d";"4e";"4f";"50";"51";"52";"53";"54";"55";"56";"57";"58";"59";"5a";"5b";"5c";"5d";"5e";"5f";"60";"61";"62";"63";"64";"65";"66";"67";"68";"69";"6a";"6b";"6c";"6d";"6e";"6f";"70";"71";"72";"73";"74";"75";"76";"77";"78";"79";"7a";"7b";"7c";"7d";"7e";"7f";"80";"81";"82";"83";"84";"85";"86";"87";"88";"89";"8a";"8b";"8c";"8d";"8e";"8f";"90";"91";"92";"93";"94";"95";"96";"97";"98";"99";"9a";"9b";"9c";"9d";"9e";"9f";"a0";"a1";"a2";"a3";"a4";"a5";"a6";"a7";"a8";"a9";"aa";"ab";"ac";"ad";"ae";"af";"b0";"b1";"b2";"b3";"b4";"b5";"b6";"b7";"b8";"b9";"ba";"bb";"bc";"bd";"be";"bf";"c0";"c1";"c2";"c3";"c4";"c5";"c6";"c7";"c8";"c9";"ca";"cb";"cc";"cd";"ce";"cf";"d0";"d1";"d2";"d3";"d4";"d5";"d6";"d7";"d8";"d9";"da";"db";"dc";"dd";"de";"df";"e0";"e1";"e2";"e3";"e4";"e5";"e6";"e7";"e8";"e9";"ea";"eb";"ec";"ed";"ee";"ef";"f0";"f1";"f2";"f3";"f4";"f5";"f6";"f7";"f8";"f9";"fa";"fb";"fc";"fd";"fe";"ff"];
	  load_index_to_hashtable indextable d;
	  load_deleted_to_hashtable deletedtable d
	end

    let dbinit () =
      dbinit_a (Filename.concat !dbdir M.basedir)

    let dbexists k =
      Hashtbl.mem indextable k && not (Hashtbl.mem deletedtable k)

    let dbget k =
      let (di,p) = Hashtbl.find indextable k in
      if Hashtbl.mem deletedtable k then
	raise Not_found
      else
	let datf = Filename.concat di "data" in
	withlock
	  (fun () ->
	    if Sys.file_exists datf then
	      let c = open_in_bin datf in
	      let l = in_channel_length c in
	      try
		if p >= l then
		  begin
		    close_in c;
		    raise (Failure ("Corrupted data file " ^ datf))
		  end;
		seek_in c p;
		let (v,_) = M.seival (c,None) in
		close_in c;
		v
	      with exc ->
		close_in c;
		raise exc
	    else
	      raise Not_found)

    let dbput k v =
      try
	let (di,p) = Hashtbl.find indextable k in
	if Hashtbl.mem deletedtable k then
	  begin
	    Hashtbl.remove deletedtable k;
	    withlock (fun () -> undelete di k)
	  end
	else
	  () (*** it's already there, do nothing ***)
      with Not_found ->
	let (d',p) = withlock (fun () -> dbfind_next_space M.basedir k) in
	withlock
	  (fun () ->
	    let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 (Filename.concat d' "index") in
	    let c = seo_hashval seoc k (ch,None) in
	    let c = seo_int32 seoc (Int32.of_int p) c in
	    seocf c;
	    close_out ch;
	    let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 (Filename.concat d' "data") in
	    let c = M.seoval v (ch,None) in
	    seocf c;
	    close_out ch;
	    Hashtbl.add indextable k (d',p)
	  )

    let dbdelete k =
      try
	let (di,p) = Hashtbl.find indextable k in
	if Hashtbl.mem deletedtable k then
	  () (*** if has already been deleted, do nothing ***)
	else
	  let ddel = Filename.concat di "deleted" in
	  let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 ddel in
	  let c = seo_hashval seoc k (ch,None) in
	  seocf c;
	  close_out ch;
	  Hashtbl.add deletedtable k ()
      with
      | Not_found -> () (*** not an entry, do nothing ***)

  end

module Dbbasic2keyiter : dbtypekeyiter = functor (M:sig type t val basedir : string val seival : (seict -> t * seict) val seoval : (t -> seoct -> seoct) end) ->
  struct
    let mutexdb : Mutex.t = Mutex.create()

    let withlock f =
      try
	Mutex.lock mutexdb;
	let r = f() in
	Mutex.unlock mutexdb;
	r
      with e ->
	Mutex.unlock mutexdb;
	raise e

    let indextable : (hashval,(string * int)) Hashtbl.t = Hashtbl.create 10000
    let deletedtable : (hashval,unit) Hashtbl.t = Hashtbl.create 100

    let rec dbinit_a d =
      if Sys.file_exists d && Sys.is_directory d then
	begin
	  List.iter
	    (fun h ->
	      dbinit_a (Filename.concat d h))
	    ["00";"01";"02";"03";"04";"05";"06";"07";"08";"09";"0a";"0b";"0c";"0d";"0e";"0f";"10";"11";"12";"13";"14";"15";"16";"17";"18";"19";"1a";"1b";"1c";"1d";"1e";"1f";"20";"21";"22";"23";"24";"25";"26";"27";"28";"29";"2a";"2b";"2c";"2d";"2e";"2f";"30";"31";"32";"33";"34";"35";"36";"37";"38";"39";"3a";"3b";"3c";"3d";"3e";"3f";"40";"41";"42";"43";"44";"45";"46";"47";"48";"49";"4a";"4b";"4c";"4d";"4e";"4f";"50";"51";"52";"53";"54";"55";"56";"57";"58";"59";"5a";"5b";"5c";"5d";"5e";"5f";"60";"61";"62";"63";"64";"65";"66";"67";"68";"69";"6a";"6b";"6c";"6d";"6e";"6f";"70";"71";"72";"73";"74";"75";"76";"77";"78";"79";"7a";"7b";"7c";"7d";"7e";"7f";"80";"81";"82";"83";"84";"85";"86";"87";"88";"89";"8a";"8b";"8c";"8d";"8e";"8f";"90";"91";"92";"93";"94";"95";"96";"97";"98";"99";"9a";"9b";"9c";"9d";"9e";"9f";"a0";"a1";"a2";"a3";"a4";"a5";"a6";"a7";"a8";"a9";"aa";"ab";"ac";"ad";"ae";"af";"b0";"b1";"b2";"b3";"b4";"b5";"b6";"b7";"b8";"b9";"ba";"bb";"bc";"bd";"be";"bf";"c0";"c1";"c2";"c3";"c4";"c5";"c6";"c7";"c8";"c9";"ca";"cb";"cc";"cd";"ce";"cf";"d0";"d1";"d2";"d3";"d4";"d5";"d6";"d7";"d8";"d9";"da";"db";"dc";"dd";"de";"df";"e0";"e1";"e2";"e3";"e4";"e5";"e6";"e7";"e8";"e9";"ea";"eb";"ec";"ed";"ee";"ef";"f0";"f1";"f2";"f3";"f4";"f5";"f6";"f7";"f8";"f9";"fa";"fb";"fc";"fd";"fe";"ff"];
	  load_index_to_hashtable indextable d;
	  load_deleted_to_hashtable deletedtable d
	end

    let dbinit () =
      dbinit_a (Filename.concat !dbdir M.basedir)

    let dbexists k =
      Hashtbl.mem indextable k && not (Hashtbl.mem deletedtable k)

    let dbget k =
      let (di,p) = Hashtbl.find indextable k in
      if Hashtbl.mem deletedtable k then
	raise Not_found
      else
	let datf = Filename.concat di "data" in
	withlock
	  (fun () ->
	    if Sys.file_exists datf then
	      let c = open_in_bin datf in
	      let l = in_channel_length c in
	      try
		if p >= l then
		  begin
		    close_in c;
		    raise (Failure ("Corrupted data file " ^ datf))
		  end;
		seek_in c p;
		let (v,_) = M.seival (c,None) in
		close_in c;
		v
	      with exc ->
		close_in c;
		raise exc
	    else
	      raise Not_found)

    let dbput k v =
      try
	let (di,p) = Hashtbl.find indextable k in
	if Hashtbl.mem deletedtable k then
	  begin
	    Hashtbl.remove deletedtable k;
	    withlock (fun () -> undelete di k)
	  end
	else
	  () (*** it's already there, do nothing ***)
      with Not_found ->
	let (d',p) = withlock (fun () -> dbfind_next_space M.basedir k) in
	withlock
	  (fun () ->
	    let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 (Filename.concat d' "index") in
	    let c = seo_hashval seoc k (ch,None) in
	    let c = seo_int32 seoc (Int32.of_int p) c in
	    seocf c;
	    close_out ch;
	    let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 (Filename.concat d' "data") in
	    let c = M.seoval v (ch,None) in
	    seocf c;
	    close_out ch;
	    Hashtbl.add indextable k (d',p)
	  )

    let dbdelete k =
      try
	let (di,p) = Hashtbl.find indextable k in
	if Hashtbl.mem deletedtable k then
	  () (*** if has already been deleted, do nothing ***)
	else
	  let ddel = Filename.concat di "deleted" in
	  let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 ddel in
	  let c = seo_hashval seoc k (ch,None) in
	  seocf c;
	  close_out ch;
	  Hashtbl.add deletedtable k ()
      with
      | Not_found -> () (*** not an entry, do nothing ***)

    let dbkeyiter f =
      Hashtbl.iter
	(fun k _ -> if not (Hashtbl.mem deletedtable k) then f k)
	indextable

  end


module DbBlacklist = Dbbasic2 (struct type t = bool let basedir = "blacklist" let seival = sei_bool seic let seoval = seo_bool seoc end)

module DbArchived = Dbbasic2 (struct type t = bool let basedir = "archived" let seival = sei_bool seic let seoval = seo_bool seoc end)
