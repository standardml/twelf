(* preserved comments 
   Florian Rabe
*)

signature COMMENTS = sig
     exception Error of string
     type comment = string * string * string  (* comment, fileName, and position string as l.c-l.c *)
     val push       : comment -> unit
     val install    : string * IDs.cid -> unit
     val installDoc : string -> unit
     val getCid  : IDs.cid -> comment option
     val getMid  : IDs.mid -> comment option
     val getDoc  : string  -> comment option
     val reset : unit -> unit
end

structure Comments : COMMENTS = struct
    exception Error of string
    type comment = string * string * string
    structure CH = CidHashTable
    val commTable : comment CH.Table = CH.new(500) (* comments installed for declarations *)
    val docCommList : comment list ref = ref nil   (* comments installed for files *)
    val current : comment list ref = ref nil       (* not yet installed comments *)
    fun getCurrent(fileName) = case ! current
       of (com as (c,f,r)) :: tl => if f = fileName then SOME com else NONE
        | nil => NONE
    fun push(com as (c,f,r)) = case getCurrent f
      of SOME _ => raise Error("only one preserved comment allowed per declaration")
       | NONE => current := com :: (! current)
    fun getCid c = CH.lookup commTable c
    fun getMid m = CH.lookup commTable (ModSyn.midToCid m)
    fun getDoc fN = List.find (fn (_,f,_) => f = fN) (! docCommList)
    fun install(fileName, c) = case getCurrent fileName
      of NONE => ()
       | SOME com => (
          CH.insert commTable(c, com);
          current := List.tl (! current)
       )
    fun installDoc fileName = case getCurrent fileName
      of NONE => ()
       | SOME com => case getDoc fileName
           of NONE => (
              docCommList := com :: ! docCommList;
              current := List.tl (! current)
           ) | SOME _ => raise Error("only one preserved comment allowed per document")
    fun reset() = (
       CH.clear commTable;
       docCommList := nil;
       current := nil
    )
end

