functor Traverse
  ((*! structure IntSyn' : INTSYN !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Traverser' : TRAVERSER)
  : TRAVERSE
  (* shares types from Traverser' *)
=
struct

  (*! structure IntSyn = IntSyn' !*)
  structure Traverser = Traverser'

  exception Error of string

local

  structure I = IntSyn
  structure T = Traverser

  (* from typecheck.fun *)

  (* inferCon (G, C) = V'

     Invariant:
     If    G |- C : V
     and  (C  doesn't contain FVars)
     then  G' |- V' : L      (for some level L)
     and   G |- V = V' : L
     else exception Error is raised.
  *)
  fun inferConW (G, I.BVar (k')) =
      let
        val I.Dec (_,V) = I.ctxDec (G, k')
      in
        Whnf.whnf (V, I.id)
      end
    | inferConW (G, I.Const(c)) = (I.constType (c), I.id)
    | inferConW (G, I.Def(d))  = (I.constType (d), I.id)
    (* no case for FVar, Skonst *)

  fun fromHead (G, I.BVar(n)) = T.bvar (Names.bvarName (G, n))
    | fromHead (G, I.Const(cid)) =
      let
        val Names.Qid (ids, id) = Names.constQid (cid)
      in
        T.const (ids, id)
      end
    (* | fromHead (G, I.Skonst (cid)) = T.skonst (Names.constName (cid)) *)
    | fromHead (G, I.Def (cid)) =
      let
        val Names.Qid (ids, id) = Names.constQid (cid)
      in
        T.def (ids, id)
      end
    (* | fromHead (G, FVar (name, _, _)) = T.fvar (name) *)
    | fromHead _ = raise Error ("Head not recognized")

  (* see also: print.fun *)
  fun impCon (I.Const (cid)) = I.constImp (cid)
    (*| imps (I.Skonst (cid)) = I.constImp (cid) *)
    | impCon (I.Def (cid)) = I.constImp (cid)
    | impCon _ = 0

  (* see also: print.fun *)
  (*
  fun dropImp (0, S) = S
    | dropImp (i, I.App (U, S)) = dropImp (i-1, S)
    | dropImp (i, I.SClo (S, s)) = I.SClo (dropImp (i, S), s)
    | dropImp _ = raise Error ("Missing implicit arguments")
  *)

  fun fromTpW (G, (I.Root (C, S), s)) =
        T.atom (fromHead (G, C),
                fromSpine (impCon C, G, (S, s), inferConW (G, C)))
    | fromTpW (G, (I.Pi ((D as I.Dec(_,V1), I.No), V2), s)) =
        T.arrow (fromTp (G, (V1, s)),
                 fromTp (I.Decl (G, I.decSub (D, s)), (V2, I.dot1 s)))
    | fromTpW (G, (I.Pi ((D, I.Maybe), V2), s)) =
      let
        val D' = Names.decUName (G, D)
      in
        T.pi (fromDec (G, (D', s)),
              fromTp (I.Decl (G, I.decSub (D', s)), (V2, I.dot1 s)))
      end
    | fromTpW _ = raise Error ("Type not recognized")

  and fromTp (G, Vs) = fromTpW (G, Whnf.whnf Vs)

  and fromObjW (G, (I.Root (C, S), s), (V, t)) =
        T.root (fromHead (G, C),
                fromSpine (impCon C, G, (S, s), inferConW (G, C)),
                fromTp (G, (V, t)))
    | fromObjW (G, (I.Lam (D, U), s), (I.Pi (_, V), t)) =
      let
        val D' = Names.decUName (G, D)
      in
        T.lam (fromDec (G, (D', s)),
               fromObj (I.Decl (G, I.decSub (D', s)),
                        (U, I.dot1 s),
                        (V, I.dot1 t)))
      end
    (* note: no case for EVars right now *)
    | fromObjW _ = raise Error ("Object not recognized")

  and fromObj (G, Us, Vt) = fromObjW (G, Whnf.whnf Us, Whnf.whnf Vt)

  and fromSpine (i, G, (I.Nil, s), Vt) = T.nils
    | fromSpine (i, G, (I.SClo (S, s'), s), Vt) =
        fromSpine (i, G, (S, I.comp (s', s)), Vt)
    | fromSpine (i, G, (I.App (U, S), s),
                 (I.Pi ((I.Dec (_, V1), _), V2), t)) =
      if i > 0                          (* drop implicit arg *)
        then fromSpine (i-1, G, (S, s),
                        Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U, s)), t)))
      else
        T.app (fromObj (G, (U, s), (V1, t)),
               fromSpine (i, G, (S, s),
                          Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U, s)), t))))

  and fromDec (G, (I.Dec (SOME(x), V), s)) =
        T.dec (x, fromTp (G, (V, s)))
    (* NONE should not occur because of call to decName *)
    (*
    | fromDec (G, (I.Dec (NONE, V), s)) =
        T.dec ("_", fromTp (G, (V, s)))
    *)

  (* ignore a : K, d : A = M, b : K = A, and skolem constants *)
  fun fromConDec (I.ConDec (c, parent, i, _, V, I.Type)) =
        SOME (T.objdec (c, fromTp (I.Null, (V, I.id))))
    | fromConDec _ = NONE

in

  val fromConDec = fromConDec

  fun const (name) =
      let val qid = case Names.stringToQid name
                      of NONE => raise Error ("Malformed qualified identifier " ^ name)
                       | SOME qid => qid
          val cidOpt = Names.constLookup qid
          fun getConDec (NONE) = raise Error ("Undeclared identifier " ^ Names.qidToString qid)
            | getConDec (SOME cid) = IntSyn.sgnLookup cid
          val conDec = getConDec cidOpt
          val _ = Names.varReset IntSyn.Null
          fun result (NONE) = raise Error ("Wrong kind of declaration")
            | result (SOME(r)) = r
      in
        result (fromConDec conDec)
      end

end  (* local ... *)

end;  (* functor Traverse *)
