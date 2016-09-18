open Ser
open Hash

val dbconfig : string -> unit

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

module Dbbasic2 : dbtype
module Dbbasic2keyiter : dbtypekeyiter

module DbBlacklist :
  sig
    val dbget : hashval -> bool
    val dbexists : hashval -> bool
    val dbput : hashval -> bool -> unit
    val dbdelete : hashval -> unit
  end

module DbArchived :
  sig
    val dbget : hashval -> bool
    val dbexists : hashval -> bool
    val dbput : hashval -> bool -> unit
    val dbdelete : hashval -> unit
  end
