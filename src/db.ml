open Ser
open Hash

let max_files_in_dir = 256
let dbdir = ref ""

let dbopen dir =
  dbdir := dir;
  if Sys.file_exists dir then
    if Sys.is_directory dir then
      ()
    else
      raise (Failure (dir ^ " is a file not a directory"))
  else
    Unix.mkdir dir 0b111111000

let dbclose () =
  ()

let rec dbfind_a d i k =
  let dk = Filename.concat d k in
  if Sys.file_exists dk then
    dk
  else if i < 20 then
    let dk' = Filename.concat d (String.sub k i 2) in
    try
      if Sys.is_directory dk' then
	dbfind_a dk' (i+2) k
      else
	raise Not_found
    with _ -> raise Not_found
  else
    raise Not_found

let dbfind d k =
  let fd = Filename.concat !dbdir d in
  try
    if Sys.is_directory fd then
      dbfind_a fd 0 (hashval_hexstring k)
    else
      raise (Failure (fd ^ " is a file not a directory"))
  with _ -> raise Not_found

let rec dbfind_next_space_a d i k =
  let l = Sys.readdir d in
  let c = ref 0 in
  for j = 0 to Array.length l - 1 do
    if String.length l.(j) = 40 then
      incr c
  done;
  if !c < max_files_in_dir || i >= 20 then
    d
  else
    let dk' = Filename.concat d (String.sub k i 2) in
    try
      if Sys.is_directory dk' then
	dbfind_next_space_a dk' (i+2) k
      else
	raise (Failure (dk' ^ " is a file not a directory"))
    with _ ->
      Unix.mkdir dk' 0b111111000;
      dk'

let dbfind_next_space d k =
  let fd = Filename.concat !dbdir d in
  try
    if Sys.is_directory fd then
      dbfind_next_space_a fd 0 (hashval_hexstring k)
    else
      raise (Failure (fd ^ " is a file not a directory"))
  with _ -> 
    Unix.mkdir fd 0b111111000;
    fd

let dbexists d k =
  try
    ignore (dbfind d k);
    true
  with Not_found -> false

let dbget d k seival =
  let f = dbfind d k in
  let c = open_in_bin f in
  let (v,_) = seival (c,None) in
  close_in c;
  v

let dbput d k v seoval =
  try
    ignore (dbfind d k)
  with Not_found ->
    let d' = dbfind_next_space d k in
    let f = Filename.concat d' (hashval_hexstring k) in
    let c = open_out_bin f in
    let o = seoval v (c,None) in
    seocf o;
    close_out c

let dbdelete d k =
  try
    let f = dbfind d k in
    Sys.remove f
  with Not_found -> ()
