(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)

functor PrintOMDoc
  ((*! structure IntSyn' : INTSYN !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   structure Constraints : CONSTRAINTS
   (*! sharing Constraints.IntSyn = IntSyn' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Formatter' : FORMATTER)
  : PRINT_XML =
struct

  (*! structure IntSyn = IntSyn' !*)
structure Formatter = Formatter'

local
  (* Shorthands *)
  structure I = IntSyn
  structure F = Formatter

  fun escape nil = nil
    | escape (#"&" :: rest) = String.explode "&amp;" @ (escape rest) 
    | escape (#"<" :: rest) = String.explode "&lt;" @ (escape rest) 
    | escape (#">" :: rest) = String.explode "&gt;" @ (escape rest) 
    | escape (c :: rest) = c :: (escape rest) 

  val Str  = F.String
  fun Str0 (s, n) = F.String0 n s
  fun Name (x) = F.String ("\"" ^ (String.implode (escape (String.explode x))) ^ "\"")
  fun Integer (n) = F.String ("\"" ^ Int.toString n ^ "\"")

  fun sexp (fmts) = F.Hbox [F.HVbox fmts]

  (* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
  fun fmtCon (G, I.BVar(n)) = 
      let
	val I.Dec (SOME n, _) = I.ctxDec (G, n)
      in 
	sexp [Str ("<OMV name = \"" ^ n ^ "\"/>")]
      end
    | fmtCon (G, I.Const(cid)) = sexp [Str "<OMS cd=\"global\" name=", Name (I.conDecName (I.sgnLookup cid)), Str "/>"]
    | fmtCon (G, I.Def(cid)) = sexp [Str "<OMS cd=\"global\" name=", Name (I.conDecName (I.sgnLookup cid)), Str "/>"]
    | fmtCon (G, I.FgnConst (csid, condec)) = sexp [Str "FngConst"]  (* FIX -cs Fri Jan 28 17:45:35 2005*)
    (* I.Skonst, I.FVar cases should be impossible *)

  (* fmtUni (L) = "L" *)
  fun fmtUni (I.Type) = Str "<OMS cd=\"LF\" name=\"Type\"/>"
    | fmtUni (I.Kind) = Str "<OMS cd=\"LF\" name=\"Kind\"/>"

  (* fmtExpW (G, (U, s)) = fmt
     
     format the expression U[s].

     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
  fun fmtExpW (G, (I.Uni(L), s)) = sexp [fmtUni L]
    | fmtExpW (G, (I.Pi((D as I.Dec(_,V1),P),V2), s)) =
      (case P (* if Pi is dependent but anonymous, invent name here *)
	 of I.Maybe => let
			 val (D' as I.Dec (SOME(x), V1')) = Names.decLUName (G, D) (* could sometimes be EName *)
			 val G' = I.Decl (G, D')
			 val fmtType = fmtExp (G, (V1', s))
		       in
	sexp [Str "<OMBIND> <OMS cd =\"LF\" name=\"pi\"/>",
	      F.Break, Str "<OMBVAR>", F.Break, Str "<OMATTR>", F.Break,
	      Str "<OMATP>", F.Break,
	      Str "<OMS cd=\"LF\" name=\"typeof\"/>", F.Break,
	      fmtType, F.Break, Str "</OMATP>", F.Break, 
	      Str "<OMV name=",  Name (x),  Str "/></OMATTR></OMBVAR>",
	      F.Break, fmtExp (G', (V2, I.dot1 s)), Str "</OMBIND>"]
		       end
	  | I.No => let
		       val G' = I.Decl (G, D)
		    in
		      sexp [Str "<OMA>", F.Break, Str "<OMS cd=\"LF\" name=\"arrow\"/>",
			    fmtExp (G, (V1, s)),
			    F.Break, (* Str "tw*no", F.Break,*) fmtExp (G', (V2, I.dot1 s)),
			    Str "</OMA>"]
		    end)
    | fmtExpW (G, (I.Root (H, S), s)) =
      (case (fmtSpine (G, (S, s)))
	 of NONE =>  fmtCon (G, H)
          | SOME fmts =>  F.HVbox [Str "<OMA>", fmtCon (G, H),
	       F.Break, sexp (fmts), Str "</OMA>"])
    | fmtExpW (G, (I.Lam(D, U), s)) = 
      let
	val (D' as I.Dec (SOME(x), V)) = Names.decLUName (G, D)
	val G' = I.Decl (G, D')
	val fmtType = fmtExp (G, (V, s))
      in
	sexp [Str "<OMBIND> <OMS cd =\"LF\" name=\"lambda\"/>",
	      F.Break, Str "<OMBVAR>", F.Break, Str "<OMATTR>", F.Break,
	      Str "<OMATP>", F.Break,
	      Str "<OMS cd=\"LF\" name=\"typeof\"/>", F.Break,
	      fmtType, F.Break, Str "</OMATP>", F.Break, 
	      Str "<OMV name=",  Name (x),  Str "/></OMATTR></OMBVAR>",
	      F.Break, fmtExp (G', (U, I.dot1 s)), Str "</OMBIND>"]
      end
    | fmtExpW (G, (I.FgnExp (csid, F), s)) = sexp [Str "FgnExp"] (* FIX -cs Fri Jan 28 17:45:43 2005 *)


    (* I.EClo, I.Redex, I.EVar not possible *)

  and fmtExp (G, (U, s)) = fmtExpW (G, Whnf.whnf (U, s))

  (* fmtSpine (G, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
  and fmtSpine (G, (I.Nil, _)) = NONE 
    | fmtSpine (G, (I.SClo (S, s'), s)) =
         fmtSpine (G, (S, I.comp(s',s)))
    | fmtSpine (G, (I.App(U, S), s)) =
      (case (fmtSpine (G, (S, s))) 
	 of NONE => SOME [fmtExp (G, (U, s))]
  	  | SOME fmts => SOME ([fmtExp (G, (U, s)), F.Break] @ fmts))



  fun fmtExpTop (G, (U, s)) = sexp [Str "<OMOBJ>", fmtExp (G, (U, s)), Str "</OMOBJ>"]

  (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
  fun fmtConDec (I.ConDec (name, parent, imp, _, V, L)) =
      let
	val _ = Names.varReset IntSyn.Null
      in
	sexp [Str "<symbol id=",  Name (name), Str ">", F.Break, Str "<type system=\"LF\">",
	      F.Break, fmtExpTop (I.Null, (V, I.id)),
	      Str "</type></symbol>"]
      end
    | fmtConDec (I.SkoDec (name, parent, imp, V, L)) =
      Str ("<! Skipping Skolem constant " ^ name ^ ">")
    | fmtConDec (I.ConDef (name, parent, imp, U, V, L, _)) =
      let
	val _ = Names.varReset IntSyn.Null
      in
	sexp [Str "<symbol id=", Name (name), Str ">",
	      F.Break, Str "<type system=\"LF\">",
	      F.Break, fmtExpTop (I.Null, (V, I.id)),
	      Str "</type></symbol>", F.Break,
	      Str "<definition id=",  Name (name ^ ".def"), F.Break, 
	      Str "for=",  Name (name), Str ">",fmtExpTop (I.Null, (U, I.id)),
	      Str "</definition>"]
      end
    | fmtConDec (I.AbbrevDef (name, parent, imp, U, V, L)) =
      let
	val _ = Names.varReset IntSyn.Null
      in
	sexp [Str "<symbol id=", Name (name),  Str ">",
	      F.Break, Str "<type system=\"LF\">",
	      F.Break, fmtExpTop (I.Null, (V, I.id)),
	      Str "</type></symbol>", F.Break,
	      Str "<definition id=",  Name (name ^ ".def"), F.Break, 
	      Str "for=",  Name (name), Str ">",fmtExpTop (I.Null, (U, I.id)),
	      Str "</definition>"]
      end
    | fmtConDec (I.BlockDec (name, _, _, _)) =
      Str ("<!-- Skipping Skolem constant " ^ name ^ "-->")

in

  (* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
  fun formatExp (G, U) = fmtExp (G, (U, I.id))
(*  fun formatSpine (G, S) = sexp (fmtSpine (G, (S, I.id))) *)
  fun formatConDec (condec) = fmtConDec (condec)

  fun expToString (G, U) = F.makestring_fmt (formatExp (G, U))
  fun conDecToString (condec) = F.makestring_fmt (formatConDec (condec))

  fun printSgn () =
      IntSyn.sgnApp (fn (cid) => (print (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
				  print "\n"))

  fun printSgnToFile path filename =
      let 
	val file = TextIO.openOut (path ^ filename)
	val _ = TextIO.output (file, "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<!-- nsgmls ex.xml -->\n<!DOCTYPE omdoc PUBLIC \"-//OMDoc//DTD OMDoc V1.2//EN\" \"dtd/omdoc.dtd\">\n\n<omdoc id=\"" ^ filename ^ "\">\n<theory id=\"global\">\n")

	val _ = IntSyn.sgnApp (fn (cid) => (TextIO.output (file, F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
				  TextIO.output (file, "\n")))
	val _ = TextIO.output (file, "</theory></omdoc>")
	val _ = TextIO.closeOut file

      in
	()
      end


end  (* local ... *)

end  (* functor PrintXml *)
