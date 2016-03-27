(* Copyright (c) 2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

let log : out_channel ref = ref stderr

let openlog () =
  log := open_out_gen [Open_wronly;Open_creat;Open_append] 0o644 (!Config.datadir ^ (if !Config.testnet then "/testnet/log" else "/log"))

let closelog () =
  close_out !log
