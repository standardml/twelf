(* External Syntax and Type Reconstruction *)
(* Author: Frank Pfenning *)

(* signature EXTSYN
   provides the interface for type reconstruction as seen
   by the parser
*)

signature EXTSYN =
sig

  (*! structure Paths : PATHS !*)

  type term				(* term *)
  type dec				(* variable declaration *)

  val lcid : string list * string * Paths.region -> term (* lower case id *)
  val ucid : string list * string * Paths.region -> term (* upper case id *)
  val quid : string list * string * Paths.region -> term (* quoted id, currently not parsed *)
  val scon : string * Paths.region -> term (* string constant *)

  (* unconditionally interpreted as such *)
  val evar : string * Paths.region -> term
  val fvar : string * Paths.region -> term

  val typ : Paths.region -> term	(* type, region for "type" *)
  val arrow : term * term -> term	(* tm -> tm *)
  val backarrow : term * term -> term	(* tm <- tm *)
  val pi : dec * term -> term           (* {d} tm *)
  val lam : dec * term -> term          (* [d] tm *)
  val app : term * term -> term		(* tm tm *)
  val hastype : term * term -> term	(* tm : tm *)
  val omitted : Paths.region -> term	(* _ as object, region for "_" *)

  (* region for "{dec}" "[dec]" etc. *)
  val dec : string option * term * Paths.region -> dec (* id : tm | _ : tm *)
  val dec0 : string option * Paths.region -> dec (* id | _  (type omitted) *)

end;  (* signature EXTSYN *)

(* signature RECON_TERM
   provides the interface to type reconstruction seen by Twelf 
*)

signature RECON_TERM =
sig

  (*! structure IntSyn : INTSYN !*)
  include EXTSYN

  exception Error of string
  val resetErrors : string -> unit      (* filename -fp *)
  val checkErrors : Paths.region -> unit

  datatype TraceMode = Progressive | Omniscient
  val trace : bool ref
  val traceMode : TraceMode ref

  (* Reconstruction jobs *)
  type job

  val jnothing : job
  val jand : job * job -> job
  val jwithctx : dec IntSyn.Ctx * job -> job
  val jterm : term -> job
  val jclass : term -> job
  val jof : term * term -> job
  val jof' : term * IntSyn.Exp -> job

  datatype Job =
      JNothing
    | JAnd of Job * Job
    | JWithCtx of IntSyn.Dec IntSyn.Ctx * Job
    | JTerm of (IntSyn.Exp * Paths.occExp) * IntSyn.Exp * IntSyn.Uni
    | JClass of (IntSyn.Exp * Paths.occExp) * IntSyn.Uni
    | JOf of (IntSyn.Exp * Paths.occExp) * (IntSyn.Exp * Paths.occExp) * IntSyn.Uni

  val recon : job -> Job
  val reconQuery : job -> Job
  val reconWithCtx : IntSyn.dctx * job -> Job
  val reconQueryWithCtx : IntSyn.dctx * job -> Job

  val termRegion : term -> Paths.region
  val decRegion : dec -> Paths.region
  val ctxRegion : dec IntSyn.Ctx -> Paths.region option
                  
  (* unimplemented for the moment *)
  val internalInst : 'a -> 'b
  val externalInst : 'a -> 'b

end;  (* signature RECON_TERM *)
