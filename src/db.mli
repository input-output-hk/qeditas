open Ser
open Hash

val dbopen : string -> unit
val dbclose : unit -> unit
val dbget : string -> hashval -> (seist -> 'a * seist) -> 'a
val dbexists : string -> hashval -> bool
val dbput : string -> hashval -> 'a -> ('a -> seosbt -> seosbt) -> unit
val dbdelete : string -> hashval -> unit
