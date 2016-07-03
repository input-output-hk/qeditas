(* Copyright (c) 2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

let log : out_channel ref = ref stderr

let openlog () =
  log := open_out_gen [Open_wronly;Open_creat;Open_append] 0o644 (!Config.datadir ^ (if !Config.testnet then "/testnet/log" else "/log"))

let closelog () =
  close_out !log

(***
 era ranges from 1 and 43 (roughly 1 + 41*4 = 165 years until final era when reward drops to 0
 era 1 is for the first 70000 blocks (1 to 70000)
 era 2 is for the next 210000 blocks (70001 to 280000)
 and so on until 8680001 when the final (unlimited) era of 43 begins.
 ***)
let era blkh =
  if blkh < 8680001L then
    let blki = Int64.to_int blkh in
    ((blki + 349999) / 210000) (*** start counting here at blkh = 1L, corresponding to Bitcoin block at height 350000 ***)
  else
    43

(*** the max block size is 500K during era 1 and doubles with each era, with a final max block size of 512M. ***)
let maxblockdeltasize blkh = 250000 lsl (era blkh)

