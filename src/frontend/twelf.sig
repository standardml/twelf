(* Front End Interface *) 
(* Author: Frank Pfenning *)

signature TWELF =
sig
  structure Print :
  sig
    val implicit : bool ref	       (* false, print implicit args *)
    val printInfix : bool ref	       (* false, print fully explicit form infix when possible *)
    val depth : int option ref	       (* NONE, limit print depth *)
    val length : int option ref	       (* NONE, limit argument length *)
    val indent : int ref	       (* 3, indentation of subterms *)
    val width : int ref		       (* 80, line width *)
    val noShadow : bool ref	       (* if true, don't print shadowed constants as "%const%" *)

    val sgn : unit -> unit	       (* print signature *)
    val prog : unit -> unit	       (* print signature as program *)
    val subord : unit -> unit	       (* print subordination relation *)
    val def : unit -> unit	       (* print information about definitions *)
    val domains : unit -> unit         (* print available constraint domains *)

    structure TeX :		       (* print in TeX format *)
    sig
      val sgn : unit -> unit	       (* print signature *)
      val prog : unit -> unit	       (* print signature as program *)
    end
  end

  structure Trace :
  sig 
    datatype 'a Spec =		       (* trace and breakpoint spec *)
      None			       (* no tracing, default *)
    | Some of 'a list		       (* list of clauses and families *)
    | All			       (* trace all clauses and families *)

    val trace : string Spec -> unit    (* trace clauses and families *)
    val break : string Spec -> unit    (* break at clauses and families *)
    val detail : int ref	       (* 0 = none, 1 = default, 2 = unify *)

    val show : unit -> unit	       (* show trace, break, and detail *)
    val reset : unit -> unit	       (* reset trace, break, and detail *)
  end

  structure Table :
  sig
    datatype Strategy = Variant | Subsumption  (* Variant | Subsumption *)

    val strategy : Strategy ref	      (* strategy used for %querytabled *)
    val strengthen : bool ref	      (* strengthenng used %querytabled *)
    val resetGlobalTable : unit -> unit (* reset global table           *)

  val top : unit -> unit    (* top-level for interactive tabled queries *)
  end

  structure Timers :
  sig
    val show : unit -> unit	       (* show and reset timers *)
    val reset : unit -> unit	       (* reset timers *)
    val check : unit -> unit	       (* display, but not no reset *)
  end

  structure OS :
  sig
    val chDir : string -> unit	       (* change working directory *)
    val getDir : unit -> string	       (* get working directory *)
    val exit : unit -> unit	       (* exit Twelf and ML *)
  end

  structure Compile :
  sig
    datatype Opt = No | LinearHeads | Indexing 
    val optimize : Opt ref
  end

  structure Recon :
  sig
    datatype TraceMode = Progressive | Omniscient
    val trace : bool ref
    val traceMode : TraceMode ref
  end

  structure Prover :
  sig
    datatype Strategy = RFS | FRS      (* F=Filling, R=Recursion, S=Splitting *)
    val strategy : Strategy ref	       (* FRS, strategy used for %prove *)
    val maxSplit : int ref	       (* 2, bound on splitting  *)
    val maxRecurse : int ref	       (* 10, bound on recursion *)
  end

  val chatter : int ref		             (* 3, chatter level *)
  val doubleCheck : bool ref	             (* false, check after reconstruction *)
  val unsafe : bool ref		             (* false, allows %assert *)
  val autoFreeze : bool ref		(* false, freezes families in meta-theorems *)
  val timeLimit : (Time.time option) ref     (* NONEe, allows timeLimit in seconds *)

  datatype Status = OK | ABORT	       (* return status *)

  val reset : unit -> unit	       (* reset global signature *)
  val loadFile : string -> Status      (* load file *)
  val loadString : string -> Status    (* load string *)
  val readDecl : unit -> Status	       (* read declaration interactively *)
  val decl : string -> Status	       (* print declaration of constant *)

  val top : unit -> unit	       (* top-level for interactive queries *)

  structure Config :
  sig
    type config			       (* configuration *)
    val suffix : string ref            (* suffix of configuration files *)
    val read : string -> config	       (* read config file *)
    val readWithout : string * config -> config 
                                       (* read config file, minus contents of another *)
    val load : config -> Status	       (* reset and load configuration *)
    val append : config -> Status      (* load configuration (w/o reset) *)
    val define : string list -> config (* explicitly define configuration *)
  end

  val make : string -> Status	       (* read and load configuration *)

  val version : string		       (* Twelf version *)

end;  (* signature TWELF *)
