(* preserved comments 
   Florian Rabe
*)

signature COMMENTS = sig
     exception Error of string
     type comment = string * string  (* comment and position string as l.c-l.c *)
     val push       : comment -> unit
     val install    : IDs.cid -> unit
     val installDoc : string -> unit
     val getCid  : IDs.cid -> comment option
     val getMid  : IDs.mid -> comment option
     val getDoc  : string  -> comment option
     val reset : unit -> unit
end

structure Comments : COMMENTS = struct
    exception Error of string
    type comment = string * string
    structure CH = CidHashTable
    val commTable : comment CH.Table = CH.new(500)
    val docCommList : (string * comment) list ref = ref nil
    val current : comment option ref = ref NONE
    fun push com = case ! current
      of SOME _ => raise Error("only one preserved comment allowed per declaration")
       | NONE => current := SOME com
    fun getCid c = CH.lookup commTable c
    fun getMid m = CH.lookup commTable (ModSyn.midToCid m)
    fun getDoc fN = case List.find (fn (f,_) => f = fN) (! docCommList)
       of NONE => NONE
        | SOME (_, s) => SOME s
    fun install c = case ! current
      of NONE => ()
       | SOME s => (
          CH.insert commTable(c, s);
          current := NONE
       )
    fun installDoc fileName = case ! current
      of NONE => ()
       | SOME s => case getDoc fileName
           of NONE => (
              docCommList := (fileName, s) :: ! docCommList;
              current := NONE
           ) | SOME _ => raise Error("only one preserved comment allowed per document")
    fun reset() = (
       CH.clear commTable;
       docCommList := nil;
       current := NONE
    )
end

