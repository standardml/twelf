(* External Syntax and Type Reconstruction *)
(* Author: Frank Pfenning *)

(* signature EXTSYN
   provides the interface for type reconstruction as seen
   by the parser
*)

signature EXTSYN =
sig

  structure Paths : PATHS

  type term				(* term *)
  type dec				(* variable declaration *)

  val lcid : string * Paths.region -> term (* lower case id *)
  val ucid : string * Paths.region -> term (* upper case id *)
  val quid : string * Paths.region -> term (* quoted id, currently not parsed *)
  val scon : string * Paths.region -> term (* string constant *)

  val app : term * term -> term		(* tm tm *)
  val arrow : term * term -> term	(* tm -> tm *)
  val backarrow : term * term -> term	(* tm <- tm *)
  val hastype : term * term -> term	(* tm : tm *)
  val omitobj : Paths.region -> term	(* _ as object, region for "_" *)
  val pi : dec * term * Paths.region -> term (* {d} tm, region for "{d}" *)
  val lam : dec * term * Paths.region -> term (* [d] tm, region for "[d]" *)
  val typ : Paths.region -> term	(* type, region for "type" *)

  val dec : string option * term -> dec	(* id : tm | _ : tm *)
  val dec0 : string option -> dec	(* id | _  (type omitted) *)

  type condec				(* constant declaration *)
  val condec : string * term -> condec	(* id : tm *)
  val condef : string option * term * term option -> condec
					(* id : tm = tm | _ : tm = tm *)

  type query				(* query *)
  val query : string option * term -> query (* ucid : tm | tm *)

end;  (* signature EXTSYN *)

(* signature VARS
   provides the function which translates free variables either
   universally (in declarations) or existentially (in queries)
*)

signature VARS =
sig
  structure IntSyn : INTSYN

  val var : string * int -> (IntSyn.Exp * IntSyn.Exp * bool ref * (IntSyn.Spine -> IntSyn.Exp)) 
end;  (* signature VARS *)

(* signature TP_RECON
   provides the interface to type reconstruction seen by Twelf 

   There are two structures with this signature,
   on translating free variables universally, the other existentially.
*)

signature TP_RECON =
sig

  structure IntSyn : INTSYN
  include EXTSYN

  exception Error of string
  val resetErrors : string -> unit	(* filename -fp *)

  type approxDec
  type approxExp
  type approxCtx = approxDec IntSyn.Ctx

  val decToApproxDec : approxCtx * dec -> approxDec
  val approxDecToDec : IntSyn.dctx * approxDec * Paths.region -> IntSyn.Dec

  val termToApproxExp : approxCtx * term -> approxExp
  val approxExpToExp : IntSyn.dctx * approxExp -> IntSyn.Exp * IntSyn.Exp

  val termToApproxExp' : approxCtx * term -> approxExp
  val approxExpToExp' : IntSyn.dctx * approxExp -> IntSyn.Exp * IntSyn.Exp

  (* val ctxToCtx : (dec * Paths.region) IntSyn.Ctx -> IntSyn.dctx *)

  val termToExp : (dec * Paths.region) IntSyn.Ctx * term
                   -> IntSyn.dctx * IntSyn.Exp * IntSyn.Exp

  val queryToQuery : query * Paths.location
                     -> IntSyn.Exp * string option * (IntSyn.Exp * string) list
                     (* (A, SOME("X"), [(Y1, "Y1"),...] *)
		     (* where A is query type, X the optional proof term variable name *)
		     (* Yi the EVars in the query and "Yi" their names *)

  val condecToConDec : condec * Paths.location * bool -> IntSyn.ConDec option * Paths.occConDec option
                     (* optional ConDec is absent for anonymous definitions *)
                     (* bool = true means that condec is an abbreviation *)
				   
end;  (* signature TP_RECON *)
