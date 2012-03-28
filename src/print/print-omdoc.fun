(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Florian Rabe *)

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
  : PRINT_OMDOC =
struct

  (*! structure IntSyn = IntSyn' !*)
structure Formatter = Formatter'

local
  (* Shorthands *)
  structure I = IntSyn

  (* The Formatter isn't really helpful for OMDoc output. So the basic functions are reimplemented here.
     indent : current indentatioin width
     nl_ind()() : newline and indent
     nl_unind()() : newline and unindent
     nl() : newline (with current indentation) *)
  val indent = ref 0
  val tabstring = "   "
  fun tabs(n) = if (n <= 0) then "" else tabstring ^ tabs(n-1)
  fun ind_reset() = (indent := 0)
  fun ind(n) = indent := !indent + n
  fun unind(n) = indent := !indent - n
  fun nl_ind() = (indent := !indent + 1; "\n" ^ tabs(!indent))
  fun nl_unind() = (indent := !indent - 1; "\n" ^ tabs(!indent))
  fun nl() = "\n" ^ tabs(!indent)

  fun escape s = let
          fun escapelist nil = nil
            | escapelist (#"&" :: rest) = String.explode "&amp;" @ (escapelist rest)
            | escapelist (#"<" :: rest) = String.explode "&lt;" @ (escapelist rest)
            | escapelist (#">" :: rest) = String.explode "&gt;" @ (escapelist rest)
            | escapelist (c :: rest) = c :: (escapelist rest)
  in
    String.implode (escapelist (String.explode s))
  end

 (* If namesafe is true during printing, the output is guaranteed to be namesafe (no duplicate names).
    But it doesn't look good. If the user knows that are no overloaded constants, namesafe can be set to false. *)
 val namesafe = ref true

  (* XML start characters: ":" | "_" | [A-Z] | [a-z], further characters: "-" | "." | [0-9] *)
  fun replace c = if (Char.isAlphaNum c) orelse (Char.contains ":_-." c) then
        (String.str c)
  else
        "_"
  fun Name (cid) = let
        val n = I.conDecName(I.sgnLookup cid)
        val name = String.translate replace n
        val start = if (Char.isAlpha (String.sub(name,0))) orelse (String.sub(name,0) = #"_") then "" else "_"
  in
        if (!namesafe) then
                start ^ name ^ "__c" ^ (Int.toString cid)
        else
                n
  end
  (* x must be the number of the varialbe in left ro right order in the context *)
  fun VarName (x,n) = let
        val name = String.translate replace n
        val start = if (Char.isAlpha (String.sub(name,0))) orelse (String.sub(name,0) = #"_") then "" else "_"
  in
        if (!namesafe) then
                start ^ name ^ "__v" ^ (Int.toString x)
        else
                n
  end

  (* Some original Formatter functions replaced with trivial functions. *)
  (* val Str  = F.String
  fun Str0 (s, n) = F.String0 n s
  fun Integer (n) = ("\"" ^ Int.toString n ^ "\"") *)
  fun Str (s) = s
  (* fun sexp (fmts) = F.Hbox [F.HVbox fmts] *)
  fun sexp (l) = String.concat l

  (* This is probably defined elsewhere, too. It's needed to check how many arguments there will be in an om:OMA element *)
  fun spineLength I.Nil = 0
    | spineLength (I.SClo (S, _)) = spineLength S
    | spineLength (I.App(_, S)) = 1 + (spineLength S)

  (* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
  fun fmtCon (G, I.BVar(x)) =
      let
        val I.Dec (SOME n, _) = I.ctxDec (G, x)
      in
        sexp [Str ("<om:OMV name=\"" ^ VarName(I.ctxLength G - x + 1,n) ^ "\"/>")]
      end
    | fmtCon (G, I.Const(cid)) = sexp [Str "<om:OMS cd=\"global\" name=\"", Name cid, Str "\"/>"]
    | fmtCon (G, I.Def(cid)) = sexp [Str "<om:OMS cd=\"global\" name=\"", Name cid, Str "\"/>"]
    | fmtCon (G, I.FgnConst (csid, condec)) = sexp [Str "FgnConst"]  (* FIX -cs Fri Jan 28 17:45:35 2005*)
    (* I.Skonst, I.FVar cases should be impossible *)

  (* fmtUni (L) = "L" *)
  fun fmtUni (I.Type) = Str "<om:OMS cd=\"twelf\" name=\"type\"/>"
    | fmtUni (I.Kind) = Str "<om:OMS cd=\"twelf\" name=\"kind\"/>"

  (* fmtExpW (G, (U, s)) = fmt

     format the expression U[s].

     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
  fun fmtExpW (G, (I.Uni(L), s), _) = sexp [fmtUni L]
    | fmtExpW (G, (I.Pi((D as I.Dec(_,V1),P),V2), s), imp) =
      (case P (* if Pi is dependent but anonymous, invent name here *)
         of I.Maybe => let
                         val (D' as I.Dec (SOME(name), V1')) = Names.decLUName (G, D) (* could sometimes be EName *)
                         val G' = I.Decl (G, D')
                         val _ = ind(1)  (* temporary indentation *)
                         val fmtBody = fmtExp (G', (V2, I.dot1 s), Int.max(0,imp - 1))
                         val _ = ind(1)
                         val fmtType = fmtExp (G, (V1', s), 0)
                         val _ = unind(2)
                         val pi = if (imp > 0) then "implicit_Pi" else "Pi"
                         val id = VarName(I.ctxLength G',name)
                       in
                                fmtBinder(pi, name, id, fmtType, fmtBody)
                       end
          | I.No => let
                       val G' = I.Decl (G, D)
                    in
                      sexp [Str "<om:OMA>", nl_ind(), Str "<om:OMS cd=\"twelf\" name=\"arrow\"/>", nl(),
                            fmtExp (G, (V1, s), 0), nl(),
                            fmtExp (G', (V2, I.dot1 s), 0), nl_unind(),
                            Str "</om:OMA>"]
                    end)
    | fmtExpW (G, (I.Root (H, S), s), _) = let
        val l = spineLength(S)
        val out = ref ""
        val _ = if (l = 0) then
                (* no arguments *)
                out := !out ^ fmtCon (G, H)
        else let
                (* an application *)
                val _ = out := !out ^ "<om:OMA>" ^ nl_ind()
                (* If there are more than two explicit arguments to an infix operator,
                   the implict and the first two explicit arguments have to be wrapped in their own om:OMA element.
                   In this case, the output will not be in normal form. *)
                val (test,cid) =
                        case H of
                           I.Const(c) => (true,c)
                         | I.Skonst(c) => (true,c)
                         | I.Def(c) => (true,c)
                         | I.NSDef(c) => (true,c)
                         | _ => (false,0)
                val imp = IntSyn.conDecImp (IntSyn.sgnLookup cid)
                val (test,args) = if test then
                        case Names.getFixity cid of
                                  Names.Fixity.Infix(_,_) => (true,imp + 2)
                                | _ => (false,0)
                else (false,0)
                val _ = if test andalso (l > args) then
                        out := !out ^ "<om:OMA>" ^ nl_ind()
                else
                        ()
        (* print constant and arguments,
           args is passed to fmtSpine so that fmtSpine can insert a closing tag after args arguments, 0 means no effect *)
        in out := !out ^ fmtCon (G, H) ^ fmtSpine (G, (S, s), args) ^ "</om:OMA>"
        end
      in
        !out
      end
    | fmtExpW (G, (I.Lam(D, U), s), imp) =
      let
        val (D' as I.Dec (SOME(name), V)) = Names.decLUName (G, D)
        val G' = I.Decl (G, D')
        val _ = ind(1)  (* temporary indentation *)
        val fmtBody = fmtExp (G', (U, I.dot1 s), Int.max(0,imp - 1))
        val _ = ind(1)
        val fmtType = fmtExp (G, (V, s), 0)
        val _ = unind(2)
        val lam = if (imp > 0) then "implicit_lambda" else "lambda"
        val id = VarName(I.ctxLength G',name)
      in
        fmtBinder(lam, name, id, fmtType, fmtBody)
      end
    | fmtExpW (G, (I.FgnExp (csid, F), s), 0) = sexp [Str "FgnExp"] (* FIX -cs Fri Jan 28 17:45:43 2005 *)

    (* I.EClo, I.Redex, I.EVar not possible *)

  and fmtExp (G, (U, s), imp) = fmtExpW (G, Whnf.whnf (U, s), imp)

  (* fmtSpine (G, (S, s), args) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
     args is the number of arguments after which </om:OMA> must be inserted, no effect if negative
  *)
  and fmtSpine (G, (I.Nil, _),_) = nl_unind()
    | fmtSpine (G, (I.SClo (S, s'), s), args) =
        fmtSpine (G, (S, I.comp(s',s)), args)
    | fmtSpine (G, (I.App(U, S), s), args) = let
        (* print first argument, 0 is dummy value *)
        val out = ref (nl() ^ fmtExp (G, (U, s), 0))
        (* close application if args reaches 0 *)
        val _ = if (args = 1) andalso (spineLength(S) > 0) then
                        out := !out ^ nl_unind() ^ "</om:OMA>"
                else
                        ()
        (* print remaining arguments *)
      in !out ^ fmtSpine (G, (S, s), args-1)
      end

  and fmtExpTop (G, (U, s), imp) = sexp [Str "<om:OMOBJ>", nl_ind(), fmtExp (G, (U, s), imp), nl_unind(), Str "</om:OMOBJ>"]

  (* top-level and shared OMDoc output, used in fmtConDec *)
  and fmtBinder(binder, varname, varid, typ, body) =
        "<om:OMBIND>" ^ nl_ind() ^ "<om:OMS cd=\"twelf\" name=\"" ^ binder ^ "\"/>" ^ nl() ^ "<om:OMBVAR><om:OMATTR>" ^ nl_ind() ^
        (if (!namesafe) then
                ("<om:OMATP><om:OMS cd=\"omdoc\" name=\"notation\"/><om:OMFOREIGN encoding=\"application/omdoc+xml\">" ^
                "<presentation for=\"#" ^ varid ^ "\"><use format=\"twelf\">" ^ varname ^
                "</use></presentation>" ^
                "</om:OMFOREIGN></om:OMATP>")
        else (* In the presentation information for variables can be omitted since it's their name anyway *)
                "")
        ^ "<om:OMATP>" ^ nl() ^
        "<om:OMS cd=\"twelf\" name=\"oftype\"/>" ^ nl() ^
        typ ^ nl() ^ "</om:OMATP>" ^ nl() ^
        "<om:OMV name=\"" ^ varid ^ "\"/>" ^ nl_unind() ^ "</om:OMATTR></om:OMBVAR>" ^ nl() ^
        body ^ nl_unind() ^ "</om:OMBIND>"
  and fmtSymbol(name, V, imp) =
        "<symbol name=\"" ^ name ^ "\">" ^ nl_ind() ^ "<type system=\"twelf\">" ^
         nl_ind() ^ fmtExpTop (I.Null, (V, I.id), imp) ^ nl_unind() ^
         "</type>" ^ nl_unind() ^ "</symbol>"
  and fmtDefinition(name, U, imp) =
        "<definition xml:id=\"" ^ name ^ ".def\" for=\"#" ^ name ^ "\">" ^ nl_ind() ^
        fmtExpTop (I.Null, (U, I.id), imp) ^ nl_unind() ^ "</definition>"
  and fmtPresentation(cid) = let
        val imp = I.conDecImp (I.sgnLookup cid)
        val fixity = Names.getFixity (cid)
        val fixString = " fixity=\"" ^ (case fixity of
                  Names.Fixity.Nonfix => "prefix"       (* case identified by @precedence = Names.Fixity.minPrefInt *)
                | Names.Fixity.Infix(prec, assoc) => (
                        case assoc of
                          Names.Fixity.Left => "infixl"
                        | Names.Fixity.Right => "infixr"
                        | Names.Fixity.None => "infix"
                )
                | Names.Fixity.Prefix(prec) => "prefix"
                | Names.Fixity.Postfix(prec) => "postfix"
        ) ^ "\""
        val precString = " precedence=\"" ^ (Int.toString (Names.Fixity.precToIntAsc(fixity))) ^ "\""
        val bracString = " bracket-style=\"lisp\" lbrack=\"(\" rbrack=\")\""
        val sepString = " separator=\" \""
        val implicitString = " implicit=\"" ^ (Int.toString imp) ^ "\""
        val useString1 = "<use format=\"twelf\""
        val useString2 = ">" ^ (escape (I.conDecName(I.sgnLookup cid))) ^ "</use>"
        val presString1 = "<presentation for=\"#" ^ (Name cid) ^ "\""
        val presString2 = "</presentation>"
  in
        presString1 ^ ">" ^ nl_ind() ^ useString1 ^ useString2 ^ nl_unind() ^ presString2 ^ nl() ^
        presString1 ^ " role=\"applied\"" ^ fixString ^ precString ^ bracString ^ sepString ^ implicitString ^
        ">" ^ nl_ind() ^ useString1 ^ useString2 ^ nl_unind() ^ presString2
  end
  (* fixity string attached to omdoc file in private element (no escaping, fixity string cannot contain ]]>) *)
  and fmtFixity(cid) = let
        val fixity = Names.getFixity (cid)
        val name = I.conDecName (I.sgnLookup cid)
      in
        if (fixity = Names.Fixity.Nonfix) then "" else
        nl() ^ "<private for=\"#" ^ (Name cid) ^ "\">" ^ nl_ind() ^
        "<data format=\"twelf\"><![CDATA[" ^ (Names.Fixity.toString fixity) ^ " " ^ name ^ ".]]></data>" ^ nl_unind() ^
        "</private>"
      end

  (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)

  fun fmtConDec (cid, I.ConDec (name, parent, imp, _, V, L)) =
      let
        val _ = Names.varReset IntSyn.Null
        val name = Name cid
      in
        fmtSymbol(name, V, imp)
      end
    | fmtConDec (_, I.SkoDec (name, parent, imp, V, L)) =
      Str ("<!-- Skipping Skolem constant " ^ name ^ "-->")
    | fmtConDec (cid, I.ConDef (name, parent, imp, U, V, L, _)) =
      let
        val _ = Names.varReset IntSyn.Null
        val name = Name cid
      in
        fmtSymbol(name, V, imp) ^ nl() ^ fmtDefinition(name, U, imp)
      end
    | fmtConDec (cid, I.AbbrevDef (name, parent, imp, U, V, L)) =
      let
        val _ = Names.varReset IntSyn.Null
        val name = Name cid
      in
        fmtSymbol(name, V, imp) ^ nl() ^ fmtDefinition(name, U, imp)
      end
    | fmtConDec (_, I.BlockDec (name, _, _, _)) =
      Str ("<!-- Skipping Skolem constant " ^ name ^ "-->")

in

  (* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
  fun formatExp (G, U, imp) = fmtExp (G, (U, I.id), imp)
(*  fun formatSpine (G, S) = sexp (fmtSpine (G, (S, I.id))) *)
  fun formatConDec (condec) = fmtConDec (condec)

  (* fun expToString (G, U) = F.makestring_fmt (formatExp (G, U, 0)) *)
  fun conDecToString (condec) = (formatConDec (condec))


  fun fmtConst cid = formatConDec (cid, IntSyn.sgnLookup cid) ^ "\n" ^ fmtPresentation(cid) ^ fmtFixity(cid)

  fun printConst cid = (namesafe := false; fmtConst cid)

  fun printSgn filename ns =
      let
        val _ = namesafe := ns
        val _ = ind_reset()
        val file = TextIO.openOut (filename)
        val OMDocPrefix =
"<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ^
"<!DOCTYPE omdoc PUBLIC \"-//OMDoc//DTD OMDoc V1.2//EN\" " ^
(* "\"https://svn.mathweb.org/repos/mathweb.org/branches/omdoc-1.2/dtd/omdoc.dtd\">\n" ^ *)
"\"../../dtd/omdoc.dtd\">\n" ^
"<omdoc xml:id=\"" ^ filename ^ "\" " ^
"xmlns=\"http://www.mathweb.org/omdoc\" " ^
"xmlns:om=\"http://www.openmath.org/OpenMath\" " ^
"version=\"1.2\">\n\n"
        val _ = TextIO.output (file, OMDocPrefix ^ "<theory xml:id=\"global\">\n\n")

        val _ = IntSyn.sgnApp (fn (cid) => (
                        (TextIO.output (file, fmtConst cid)) ;
                        TextIO.output (file, "\n\n")
                )
        )
        val _ = TextIO.output (file, "</theory>\n\n</omdoc>")
        val _ = TextIO.closeOut file

      in
        ()
      end


end  (* local ... *)

end  (* functor PrintXml *)
