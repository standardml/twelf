(* Front End Interface *)
(* Author: Frank Pfenning *)

signature TWELF =
sig
  structure Print :
  sig
    val implicit : bool ref	      (* false, print implicit args *)
    val depth : int option ref	      (* NONE, limit print depth *)
    val length : int option ref	      (* NONE, limit argument length *)
    val indent : int ref	      (* 3, indentation of subterms *)
    val width : int ref		      (* 80, line width *)
  end

  structure Timers :
  sig
    val show : unit -> unit	      (* show and reset timers *)
    val reset : unit -> unit	      (* reset timers *)
    val check : unit -> unit	      (* display, but not no reset *)
  end

  structure OS :
  sig
    val chDir : string -> unit	      (* change working directory *)
    val getDir : unit -> string	      (* get working directory *)
    val exit : unit -> unit	      (* exit Twelf and ML *)
  end

  structure Compile :
  sig
    val optimize : bool ref
  end

  structure Prover :
  sig
    datatype Strategy = RFS | FRS     (* F=Filling, R=Recursion, S=Splitting *)
    val strategy : Strategy ref	      (* FRS, strategy used for %prove *)
    val maxSplit : int ref	      (* 2, bound on splitting  *)
    val maxRecurse : int ref	      (* 10, bound on recursion *)
  end

  val chatter : int ref		      (* 3, chatter level *)
  val doubleCheck : bool ref	      (* false, check after reconstruction *)

  datatype Status = OK | ABORT	      (* return status *)

  val reset : unit -> unit	      (* reset global signature *)
  val loadFile : string -> Status     (* load file *)
  val readDecl : unit -> Status	      (* read declaration interactively *)
  val decl : string -> Status	      (* print declaration of constant *)

  val top : unit -> unit	      (* top-level for interactive queries *)

  structure Config :
  sig
    type config			      (* configuration *)
    val read : string -> config	      (* read config file *)
    val load : config -> Status	      (* reset and load configuration *)
    val define : string list -> config (* explicitly define configuration *)
  end

  val version : string		      (* Twelf version *)
end;  (* signature TWELF *)
