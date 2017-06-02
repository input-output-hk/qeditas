open Logic
open Hash
open Mathdata

val check_theoryspec : theoryspec -> (theory * gsign) option

val check_signaspec :
  (hashval option -> hashval -> stp -> bool) -> (hashval option -> hashval ->
  bool) -> hashval option -> theory -> stree option -> signaspec ->
  (gsign * hashval list) option

val check_doc :
  (hashval option -> hashval -> stp -> bool) -> (hashval option -> hashval ->
  bool) -> hashval option -> theory -> stree option -> doc ->
  (gsign * hashval list) option
