
structure Rep =
struct

structure I = IntSyn
structure S = Syntax

fun defSize x = (case x of 
   		       Sgn.DEF_TERM y => S.size_term y
		     | Sgn.DEF_TYPE y => S.size_tp y)

fun cidSize cid = (case I.sgnLookup cid of 
   I.ConDec(_,_,_,_,_,I.Type) => S.size_tp (S.typeOf (Sgn.classifier cid))
 | I.ConDec(_,_,_,_,_,I.Kind) => S.size_knd (S.kindOf (Sgn.classifier cid))
 | I.ConDef(_,_,_,_,_,_,_) => defSize(Sgn.def cid)
 | I.AbbrevDef(_,_,_,_,_,_) => defSize(Sgn.def cid)
 | _ => 0)

fun o_cidSize cid = (case I.sgnLookup cid of 
   I.ConDec(_,_,_,_,_,I.Type) => S.size_tp (S.typeOf (Sgn.o_classifier cid))
 | I.ConDec(_,_,_,_,_,I.Kind) => S.size_knd (S.kindOf (Sgn.o_classifier cid))
 | I.ConDef(_,_,_,_,_,_,_) => defSize(Sgn.o_def cid)
 | I.AbbrevDef(_,_,_,_,_,_) => defSize(Sgn.o_def cid)
 | _ => 0)


open SMLofNJ.Cont

(* val l : (Syntax.term * Syntax.tp) list ref = ref [] *)
val k : Reductio.eq_c option ref = ref NONE


exception Crap
fun sanityCheck cid = ((case I.sgnLookup cid of 
   I.ConDec(_,_,_,_,_,I.Type) => (Reductio.check_plusconst_type (Sgn.typeOf (Sgn.classifier cid)))
 | I.ConDec(_,_,_,_,_,I.Kind) => (Reductio.check_kind ([], Sgn.kindOf (Sgn.classifier cid)))
 | I.ConDef(_,_,_,_,_,I.Type,_) => let val Sgn.DEF_TERM y = Sgn.def cid
				     val Syntax.tclass z = Sgn.classifier cid 
				 in
(*				     l := (y,z):: !l; *)
				     Reductio.check ([], y, z) 
				 end
 | I.ConDef(_,_,_,_,_,I.Kind,_) => let val Sgn.DEF_TYPE y = Sgn.def cid
				     val Syntax.kclass z = Sgn.classifier cid 
				 in
				     Reductio.check_type  Reductio.CON_LF (Syntax.explodeKind z, y) 
				 end
 | I.AbbrevDef(_,_,_,_,_,I.Type) => let val Sgn.DEF_TERM y = Sgn.def cid
				     val Syntax.tclass z = Sgn.classifier cid 
				 in
(*				     l := (y,z):: !l; *)
				     Reductio.check ([], y, z) 
				 end
 | I.AbbrevDef(_,_,_,_,_,I.Kind) => let val Sgn.DEF_TYPE y = Sgn.def cid
				     val Syntax.kclass z = Sgn.classifier cid 
				 in
				     Reductio.check_type Reductio.CON_LF (Syntax.explodeKind z, y) 
				 end
 | _ => true (* we're not checking block declarations or anything else like that *))
handle Syntax.Syntax _ => (print ("--> " ^ Int.toString cid); raise Match))



fun gen_graph n autoCompress =
    let
	val _ = autoCompress n 
	fun sanity n = if n < 0 then true else 
		       (sanity (n-1) andalso (if sanityCheck n then true else (print ("insane: <" ^ (Int.toString n) ^ ">\n"); raise Crap)) )
	val _ = sanity n 
	val pairs = List.tabulate (n+1, (fn x => ( o_cidSize x, cidSize x) ))
	val s = foldl op^ "" 
		      (map (fn (x,y) => 
			       Int.toString x ^ " " ^ Int.toString y ^ "\n" ) pairs) 
	val f = TextIO.openOut "/tmp/graph"
	val _ = TextIO.output(f,s)
	val _ = TextIO.closeOut(f)
    in
	()
    end
(* DEBUG  handle Reductio.Matching2 s => (print "doesn'tmatch"; k := SOME s); *)

(* fun gg n = (Compress.sgnReset(); gen_graph n
	    (fn n => Compress.sgnAutoCompressUpTo n Compress.naiveModes)) *)

(* Syntax.size_term (Option.valOf(#o_def (Compress.sgnLookup n))) *)

open Reductio
end

(*
fun autoCompress n modeFinder =
    let
(*	val rep = Twelf.Names.lookup "represents"
	val rep_z = Twelf.Names.lookup "represents_z"
	val rep_s = Twelf.Names.lookup "represents_s" *)
    in
	Compress.sgnReset();
	Compress.sgnAutoCompressUpTo(n)
    (* Syntax.size_term (Option.valOf(#o_def (Compress.sgnLookup n))) *)
    end
*)
