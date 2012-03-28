(* Meta syntax *)
(* Author: Carsten Schuermann *)

functor MetaSyn ((*! structure IntSyn' : INTSYN !*)
                 structure Whnf : WHNF
                 (*! sharing Whnf.IntSyn = IntSyn' !*)
                   )
  : METASYN =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

   type Var = int

  datatype Mode =                       (* Mode                       *)
    Bot                                 (* M ::= Bot                  *)
  | Top                                 (*     | Top                  *)

  datatype Prefix =                     (* Prefix P := *)
    Prefix of IntSyn.dctx               (* G   declarations           *)
            * Mode IntSyn.Ctx           (* Mtx modes                  *)
            * int IntSyn.Ctx            (* Btx splitting depths       *)

  datatype State =                      (* State S :=                 *)
    State of string                     (*             [name]         *)
             * Prefix                   (*             G; Mtx; Btx    *)
             * IntSyn.Exp               (*             |- V           *)

  datatype Sgn =                        (* Interface signature        *)
    SgnEmpty                            (* IS ::= .                   *)
  | ConDec of IntSyn.ConDec * Sgn       (*      | c:V, IS             *)

  local
    structure I = IntSyn

    (* createEVarSpineW (G, (V, s)) = ((V', s') , S')

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)
    fun createEVarSpine (G, Vs) = createEVarSpineW (G, Whnf.whnf Vs)
    and createEVarSpineW (G, Vs as (I.Uni I.Type, s)) = (I.Nil, Vs) (* s = id *)
      | createEVarSpineW (G, Vs as (I.Root _, s)) = (I.Nil, Vs)   (* s = id *)
      | createEVarSpineW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =
        let
          val X = I.newEVar (G, I.EClo (V1, s))
          val (S, Vs) = createEVarSpine (G, (V2, I.Dot (I.Exp (X), s)))
        in
          (I.App (X, S), Vs)
        end

    (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomConst (G, H) =
      let
        val cid = (case H
                     of (I.Const cid) => cid
                      | (I.Skonst cid) => cid)
        val V = I.constType cid
        val (S, Vs) = createEVarSpine (G, (V, I.id))
      in
        (I.Root (H, S), Vs)
      end

    (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomBVar (G, k) =
      let
        val I.Dec (_, V) = I.ctxDec (G, k)
        val (S, Vs) = createEVarSpine (G, (V, I.id))
      in
        (I.Root (I.BVar (k), S), Vs)
      end

  in
    val createAtomConst = createAtomConst
    val createAtomBVar = createAtomBVar
  end

end (* functor MetaSyn *)







