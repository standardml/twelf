(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)

functor CPrint ((*! structure IntSyn' : INTSYN !*)
                (*! structure CompSyn' : COMPSYN !*)
                (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                structure Print: PRINT
                (*! sharing Print.IntSyn = IntSyn' !*)
                structure Formatter : FORMATTER
                  sharing Print.Formatter = Formatter
                structure Names: NAMES
                (*! sharing Names.IntSyn = IntSyn' !*)
                  )
  : CPRINT =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)

  local
    open CompSyn
  in

    fun compose(IntSyn.Null, G) = G
      | compose(IntSyn.Decl(G, D), G') = IntSyn.Decl(compose(G, G'), D)

    (* goalToString (G, g) where G |- g  goal *)
    fun goalToString t (G, Atom(p)) =
         t ^ "SOLVE   " ^ Print.expToString (G, p) ^ "\n"
      | goalToString t (G, Impl (p,A,_,g)) =
         t ^ "ASSUME  " ^ Print.expToString (G, A) ^ "\n" ^
         (clauseToString (t ^ "\t") (G, p)) ^
         goalToString t (IntSyn.Decl(G, IntSyn.Dec(NONE, A)), g) ^ "\n"
      | goalToString t (G, All(D,g)) =
         let
           val D' = Names.decLUName (G, D)
         in
           t ^ "ALL     " ^
           Formatter.makestring_fmt (Print.formatDec (G, D')) ^ "\n" ^
           goalToString t (IntSyn.Decl (G, D'), g) ^ "\n"
         end

    (* auxToString (G, r) where G |- r auxgoal *)
    and auxToString t (G, Trivial) = ""
      | auxToString t (G, UnifyEq(G', p1, N, ga)) =
         t ^ "UNIFYEqn  " ^ Print.expToString (compose(G',G), p1) ^ " = " ^
                       Print.expToString (compose(G',G), N) ^ "\n" ^
         auxToString t (G, ga)

    (* clauseToString (G, r) where G |- r  resgoal *)
    and clauseToString t (G, Eq(p)) =
         t ^ "UNIFY   " ^ Print.expToString (G, p) ^ "\n"
      | clauseToString t (G, Assign(p, ga)) =
         (t ^ "ASSIGN  " ^ (Print.expToString (G, p)  handle _ => "<exc>")
         ^ "\n" ^ (auxToString t (G, ga)))
      | clauseToString t (G, And(r, A, g)) =
         clauseToString t (IntSyn.Decl(G, IntSyn.Dec(NONE, A)), r) ^
         goalToString t (G, g)
      | clauseToString t (G, In(r, A, g)) =
         let
           val D = Names.decEName (G, IntSyn.Dec (NONE, A))
         in
           clauseToString t (IntSyn.Decl(G, D), r) ^
           t ^ "META    " ^ Print.decToString (G, D) ^ "\n" ^
           goalToString t (G, g)
         end
      | clauseToString t (G, Exists(D, r)) =
         let
           val D' = Names.decEName (G, D)
         in
           t ^ "EXISTS  " ^
           (Print.decToString (G, D') handle _ => "<exc>") ^ "\n" ^
           clauseToString t (IntSyn.Decl(G, D'), r)
         end

      | clauseToString t (G, Axists(D as IntSyn.ADec(SOME(n), d), r)) =
         let
           val D' = Names.decEName (G, D)
         in
           t ^ "EXISTS'  " ^
           (Print.decToString (G, D') handle _ => "<exc>") ^ "\n" ^
           clauseToString t (IntSyn.Decl(G, D'), r)
         end

    fun subgoalsToString t (G, True) = t ^ "True "
      | subgoalsToString t (G, Conjunct(Goal, A, Sg)) =
        t  ^ goalToString t (IntSyn.Decl(G,IntSyn.Dec(NONE, A)), Goal) ^ " and " ^ subgoalsToString t (G, Sg)

    (* conDecToString (c, clause) printed representation of static clause *)
    fun conDecToString (c, SClause(r)) =
        let
          val _ = Names.varReset IntSyn.Null
          val name = IntSyn.conDecName (IntSyn.sgnLookup c)
          val l = String.size name
        in
          name ^ (if l > 6 then ":\n" else ":") ^
          (clauseToString "\t" (IntSyn.Null, r) ^ "\n")
        end
      | conDecToString (c, Void) =
          Print.conDecToString (IntSyn.sgnLookup c) ^ "\n\n"

    (* sProgToString () = printed representation of static program *)
    fun sProgToString () =
        let val (size, _) = IntSyn.sgnSize ()
            fun ts (cid) = if cid < size
                             then conDecToString (cid, CompSyn.sProgLookup cid)
                                  ^ ts (cid+1)
                           else ""
         in
           ts 0
         end

    (* dProgToString (G, dProg) = printed representation of dynamic program *)
    fun dProgToString (DProg (IntSyn.Null, IntSyn.Null)) = ""
      | dProgToString (DProg (IntSyn.Decl(G,IntSyn.Dec(SOME x,_)),
                       IntSyn.Decl(dPool, CompSyn.Dec (r,_,_)))) =
          dProgToString (DProg (G,dPool))
          ^ "\nClause    " ^ x ^ ":\n"
          ^ clauseToString "\t" (G, r)
      | dProgToString (DProg (IntSyn.Decl(G, IntSyn.Dec(SOME x,A)),
                       IntSyn.Decl(dPool, CompSyn.Parameter))) =
         dProgToString (DProg (G, dPool))
         ^ "\nParameter " ^ x ^ ":\t"
         ^ Print.expToString (G, A)
     (* case for CompSyn.BDec is still missing *)



  end  (* local open ... *)

end; (* functor CPrint *)
