(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

let stringconfigvars = [
("datadir",Config.datadir);
("ctreedatadir",Config.ctreedatadir);
("chaindatadir",Config.chaindatadir)
];;
let boolconfigvars = [
("staking",Config.staking)
];;
let intconfigvars = [
("port",Config.port);
("rpcport",Config.rpcport);
("socksport",Config.socksport)
];;
let stringoptionconfigvars = [
("ip",Config.ip)
];;
let intoptionconfigvars = [
("socks",Config.socks);
];;

exception Done

let process_config_line l =
  let ll = String.length l in
  begin
    try
      List.iter
	(fun (v,r) ->
	  let vl = String.length v in
	  if ll > 1 + vl && String.sub l 0 (vl) = v && l.[vl] = '=' then
	    begin
	      r := String.sub l (vl+1) (ll-(vl+1));
	      raise Done
	    end
	  )
	stringconfigvars;
      List.iter
	(fun (v,r) ->
	  let vl = String.length v in
	  if ll > 1 + vl && String.sub l 0 (vl) = v && l.[vl] = '=' then
	    let s = String.sub l (vl+1) (ll-(vl+1)) in
	    begin
	      r := (s = "1" || s = "t" || s = "true");
	      raise Done
	    end
	  )
	boolconfigvars;
      List.iter
	(fun (v,r) ->
	  let vl = String.length v in
	  if ll > 1 + vl && String.sub l 0 (vl) = v && l.[vl] = '=' then
	    begin
	      r := int_of_string (String.sub l (vl+1) (ll-(vl+1)));
	      raise Done
	    end
	  )
	intconfigvars;
      List.iter
	(fun (v,r) ->
	  let vl = String.length v in
	  if ll > 1 + vl && String.sub l 0 (vl) = v && l.[vl] = '=' then
	    begin
	      r := Some(String.sub l (vl+1) (ll-(vl+1)));
	      raise Done
	    end
	  )
	stringoptionconfigvars;
      List.iter
	(fun (v,r) ->
	  let vl = String.length v in
	  if ll > 1 + vl && String.sub l 0 (vl) = v && l.[vl] = '=' then
	    begin
	      r := Some(int_of_string (String.sub l (vl+1) (ll-(vl+1))));
	      raise Done
	    end
	  )
	intoptionconfigvars;
      raise Not_found
    with Done -> ()
  end

let process_config_file () =
  let fn = Filename.concat !Config.datadir "qeditas.conf" in
  if Sys.file_exists fn then
    begin
      let ch = open_in fn in
      try
	while true do
	  let l = input_line ch in
	  try
	    process_config_line l
	  with Not_found ->
	    Printf.printf "Do not understand %s in qeditas.conf; skipping\n" l
	done
      with End_of_file -> ()
    end
  else
    Printf.printf "No qeditas.conf file found. Using default configuration.\n";;

let process_config_args () =
  let a = Array.length Sys.argv in
  for i = 1 to a-1 do
    let arg = Sys.argv.(i) in
    if String.length arg > 1 && arg.[0] = '-' then
      try
	process_config_line (String.sub arg 1 ((String.length arg) - 1))
      with Not_found -> ()
  done;;
