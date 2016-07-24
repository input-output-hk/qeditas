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
    val dbget : hashval -> M.t
    val dbexists : hashval -> bool
    val dbput : hashval -> M.t -> unit
    val dbdelete : hashval -> unit
  end

module Dbbasic : dbtype = functor (M:sig type t val basedir : string val seival : (seict -> t * seict) val seoval : (t -> seoct -> seoct) end) ->
  struct
    let cache1 : (hashval,M.t) Hashtbl.t ref = ref (Hashtbl.create max_in_cache)
    let cache2 : (hashval,M.t) Hashtbl.t ref = ref (Hashtbl.create max_in_cache)

    let add_to_cache (k,v) =
      if Hashtbl.length !cache1 < max_in_cache then
	Hashtbl.add !cache1 k v
      else
	let h = !cache2 in
	cache2 := !cache1;
	Hashtbl.clear h;
	Hashtbl.add h k v;
	cache1 := h

    let del_from_cache k =
      Hashtbl.remove !cache1 k;
      Hashtbl.remove !cache2 k

    let dbexists k =
      try
	if Hashtbl.mem !cache1 k then
	  true
	else if Hashtbl.mem !cache2 k then
	  begin
	    let v = Hashtbl.find !cache2 k in
	    add_to_cache (k,v);
	    true
	  end
	else
	  begin
	    let (di,_) = dbfind M.basedir k in
	    try
	      find_in_deleted di k;
	      raise Exit
	    with Not_found -> true
	  end
      with
      | Exit -> false
      | Not_found -> false

    let dbget k =
      try
	Hashtbl.find !cache1 k
      with Not_found ->
	try
	  let v = Hashtbl.find !cache2 k in
	  add_to_cache (k,v);
	  v
	with Not_found ->
	  let (di,p) = dbfind M.basedir k in
	  try
	    find_in_deleted di k;
	    raise Exit
	  with
	  | Exit -> raise Not_found
	  | Not_found ->
	    let datf = Filename.concat di "data" in
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
		add_to_cache (k,v);
		v
	      with exc ->
		close_in c;
		raise exc
	    else
	      raise Not_found

    let dbput k v =
      try
	let (di,p) = dbfind M.basedir k in
	try
	  find_in_deleted di k;
	  undelete di k
	with Not_found -> () (*** otherwise, it's already there, do nothing ***)
      with Not_found ->
	let (d',p) = dbfind_next_space M.basedir k in
	let indl = load_index d' in
	let indl2 = List.merge (fun (h',p') (k',q') -> compare h' k') (List.rev indl) [(k,p)] in
(*	let ch = open_out_bin 0b110110000 (Filename.concat d' "index") in *)
	let ch = open_out_bin (Filename.concat d' "index") in
	List.iter
	  (fun (h,q) ->
	    let c = seo_hashval seoc h (ch,None) in
	    let c = seo_int32 seoc (Int32.of_int q) c in
	    seocf c)
	  indl2;
	close_out ch;
	let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 (Filename.concat d' "data") in
	let c = M.seoval v (ch,None) in
	seocf c;
	close_out ch

    let dbdelete k =
      try
	let (di,p) = dbfind M.basedir k in
	try
	  find_in_deleted di k (*** if has already been deleted, do nothing ***)
	with Not_found ->
	  let ddel = Filename.concat di "deleted" in
	  let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 ddel in
	  let c = seo_hashval seoc k (ch,None) in
	  seocf c;
	  close_out ch;
	  del_from_cache k;
	  let nd = count_deleted di in
	  if nd = count_index di then (*** easy case: all entries in the dir have been deleted; a common case would likely be when a dir has 1 entry and it gets deleted ***)
	    begin
	      Sys.remove ddel;
	      Sys.remove (Filename.concat di "index");
	      Sys.remove (Filename.concat di "data")
	    end
	  else if count_deleted di > defrag_limit then
	    defrag di M.seival M.seoval
      with Not_found -> () (*** not an entry, do nothing ***)

  end

module DbBlacklist = Dbbasic (struct type t = bool let basedir = "blacklist" let seival = sei_bool seic let seoval = seo_bool seoc end)

module DbArchived = Dbbasic (struct type t = bool let basedir = "archived" let seival = sei_bool seic let seoval = seo_bool seoc end)
