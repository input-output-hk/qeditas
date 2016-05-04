open Ser
open Hash

val dbopen : string -> unit
val dbclose : unit -> unit
val dbget : string -> hashval -> (seict -> 'a * seict) -> 'a
val dbexists : string -> hashval -> bool
val dbput : string -> hashval -> 'a -> ('a -> seoct -> seoct) -> unit
val dbdelete : string -> hashval -> unit
