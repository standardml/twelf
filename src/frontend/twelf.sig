(* Front End Interface *) 
(* Author: Frank Pfenning *)

signature TWELF =
sig
  structure Print :
  sig
    val implicit : bool ref	       (* false, print implicit args *)
    val depth : int option ref	       (* NONE, limit print depth *)
    val length : int option ref	       (* NONE, limit argument length *)
    val indent : int ref	       (* 3, indentation of subterms *)
    val width : int ref		       (* 80, line width *)

    val sgn : unit -> unit	       (* print signature *)
    val prog : unit -> unit	       (* print signature as program *)
    val subord : unit -> unit	       (* print subordination relation *)
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
    val optimize : bool ref		(* true, optimize clauses *)
  end

  structure Table : 
  sig 
    datatype Strategy = Variant | Subsumption

    val strategy : Strategy ref		(* Variant, tabling strategy *)
    val strengthen : bool ref		(* false, tabling optimization *)

    val top : unit -> unit		(* Top-level for tabled queries *)
  end 

  structure Recon :
  sig
    datatype TraceMode = Progressive | Omniscient
    val trace : bool ref		(* false, trace term reconstruction *)
    val traceMode : TraceMode ref	(* Omniscient, trace mode *)
  end

  structure Prover :
  sig
    datatype Strategy = RFS | FRS      (* F=Filling, R=Recursion, S=Splitting *)
    val strategy : Strategy ref	       (* FRS, strategy used for %prove *)
    val maxSplit : int ref	       (* 2, bound on splitting  *)
    val maxRecurse : int ref	       (* 10, bound on recursion *)
  end

  val chatter : int ref		       (* 3, chatter level *)
  val doubleCheck : bool ref	       (* false, check after reconstruction *)
  val unsafe : bool ref		       (* false, allows %assert *)

  datatype Status = OK | ABORT	       (* return status *)

  val reset : unit -> unit	       (* reset global signature *)
  val loadFile : string -> Status      (* load file *)
  val readDecl : unit -> Status	       (* read declaration interactively *)
  val decl : string -> Status	       (* print declaration of constant *)

  val top : unit -> unit	       (* top-level for interactive queries *)

  structure Config :
  sig
    type config			       (* configuration *)
    val suffix : string ref            (* suffix of configuration files *)
    val read : string -> config	       (* read config file *)
    val load : config -> Status	       (* reset and load configuration *)
    val append : config -> Status      (* load configuration (w/o reset) *)
    val define : string list -> config (* explicitly define configuration *)
  end

  val make : string -> Status	       (* read and load configuration *)

  val version : string		       (* Twelf version *)

end;  (* signature TWELF *)
