(* Weak Head-Normal Forms *)
(* Author: Frank Pfenning, Carsten Schuermann *)

functor Whnf (structure IntSyn' : INTSYN
	      structure Pattern : PATTERN
	         sharing Pattern.IntSyn = IntSyn')
  : WHNF =
struct
  structure IntSyn = IntSyn'

  (*
     Weak Head-Normal Form (whnf)

     whnf ::= (L, s) | (Pi DP. U, s)
            | (Root(n,S), id) | (Root(c,S), id) | (Root(d,S), id) | (Root(F[s'], S), id)
            | (Lam D. U, s) | (X, s) where X is uninstantiated, X of base type
                                     during type reconstruction, X might have variable type

     Normal Form (nf)

	UA ::= L | Pi (DA,P). UA
             | Root(n,SA) | Root(c,SA) | Root(d,SA) |
             | Lam DA. UA
	DA ::= x:UA
	SA ::= Nil | App (UA, SA)

     Existential Normal Form (enf)

     Existential normal forms are like normal forms, but also allows
     X[s] where X is uninstantiated with no particular restriction on s
     or type of X.

     An existential normal form is a hereditary weak head-normal form.
  *)

  local 
    open IntSyn

    (* appendSpine ((S1, s1), (S2, s2)) = S' 

       Invariant:
       If    G |- s1 : G1   G1 |- S1 : V1' > V1 
       and   G |- s2 : G2   G2 |- S2 : V2  > V2'
       and   G |- V1 [s1] == V2 [s2]
       then  G |- S' : V1' [s1] > V2' [s2]   
    *)
    fun appendSpine ((Nil, s1), Ss2) = SClo Ss2
      | appendSpine ((App (U1, S1), s1), Ss2) =
          App (EClo (U1, s1), appendSpine ((S1, s1), Ss2))
      | appendSpine ((SClo (S1, s1'), s1), Ss2) =
	  appendSpine ((S1, comp(s1', s1)), Ss2)

    (* whnfRedex ((U, s1), (S, s2)) = (U', s')

       Invariant:
       If    G |- s1 : G1   G1 |- U : V1,   (U,s1) whnf 
	     G |- s2 : G2   G2 |- S : V2 > W2
	     G |- V1 [s1] == V2 [s2] == V : L
       then  G |- s' : G',  G' |- U' : W'
       and   G |- W'[s'] == W2[s2] == W : L
       and   G |- U'[s'] == (U[s1] @ S[s2]) : W
       and   (U',s') whnf

       Effects: EVars may be lowered to base type.
    *)
    fun whnfRedex (Us, (SClo (S, s2'), s2)) =
          whnfRedex (Us, (S, comp (s2', s2)))
      | whnfRedex (Us as (Root R, s1), (Nil, s2)) = Us
      | whnfRedex ((Root (H1, S1), s1), (S2, s2)) =
	  (* S2 = App _, only possible if term is not eta-expanded *)
	  (Root (H1, appendSpine ((S1, s1), (S2, s2))), id)
      | whnfRedex ((Lam (Dec (_, V2), U1), s1), (App (U2, S), s2)) =
	  whnfRedex (whnf (U1, Pattern.dotEta (frontSub (Exp (U2, V2), s2), s1)), (S, s2)) 
      | whnfRedex (Us as (Lam _, s1), _) = Us  (* S2[s2] = Nil *)
      | whnfRedex (Us as (EVar _, s1), (Nil, s2)) = Us
      | whnfRedex (Us as (X as EVar _, s1), Ss2) = 
	  (* Ss2 must be App, since prior cases do not apply *)
	  (* lower X results in redex, optimize by unfolding call to whnfRedex *)
	  (lower X; whnfRedex (whnf Us, Ss2))
      (* Uni and Pi can arise after instantiation of EVar X : K *)
      | whnfRedex (Us as (Uni _, s1), _) = Us	(* S2[s2] = Nil *)
      | whnfRedex (Us as (Pi _, s1), _) = Us	(* S2[s2] = Nil *)
      (* Other cases impossible since (U,s1) whnf *)

    (* lower (X) = (), effect instantiates X

       Invariant:
       If    G |- X : (Pi x:V''.V')
       then  X := Lam x:V''. X'  where  G, x:V'' |- X' : V'

       Effects: X is instantiated
    *)
    (* possible optimization: lower all the way to base type in one step *)
    and lower (EVar (r, V, nil)) = lower' (r, whnf (V, id))
      | lower (EVar _) =
        (* It is not clear if this case can happen *)
        (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
        raise Error "Typing ambiguous -- constraint of functional type cannot be simplified"
    and lower' (r, (Pi ((D', _), V'), s')) = 
          (r := SOME (Lam (decSub (D', s'), newEVar (EClo (V', dot1 s')))))
        (* no other cases possible by well-typing invariant *)

    (* whnfRoot ((H, S), s) = (U', s')

       Invariant:
       If    G |- s : G1      G1 |- H : V
			      G1 |- S : V > W
       then  G |- s' : G'     G' |- U' : W'
       and   G |- W [s] = W' [s'] : L

       Effects: EVars may be instantiated when lowered
    *)
    and whnfRoot ((BVar (k), S), s)   =
        (case bvarSub (k, s)
	   of Idx (k) => (Root (BVar (k), SClo (S, s)), id)
	    | Exp (U,V) => whnfRedex (whnf (U, id), (S, s)))
      | whnfRoot ((FVar (name, V, s'), S), s) =
	 (Root (FVar (name, V, comp (s', s)), SClo (S, s)), id)
      | whnfRoot ((H, S), s) =
	 (Root (H, SClo (S, s)), id)

    (* whnf (U, s) = (U', s')

       Invariant:
       If    G |- s : G'    G' |- U : V
       then  G |- s': G''   G''|- U' : V'
       and   G |- V [s] == V' [s'] == V'' : L  
       and   G |- U [s] == U' [s'] : V'' 
       and   (U', s') whnf
    *)
    (*
       Possible optimization :
         Define whnf of Root as (Root (n , S [s]), id)
	 Fails currently because appendSpine does not necessairly return a closure  -cs
	 Advantage: in unify, abstract... the spine needn't be treated under id, but under s
    *)
    and whnf (Us as (Uni _, s)) = Us
      | whnf (Us as (Pi _, s)) = Us
      (* simple optimization (C@S)[id] = C@S[id] *)
      (* applied in Twelf 1.1 *)
      (* Sat Feb 14 20:53:08 1998 -fp *)
      | whnf (Us as (Root _, Shift (0))) = Us
      | whnf (Root R, s) = whnfRoot (R, s)
      | whnf (Redex (U, S), s) = whnfRedex (whnf (U, s), (S, s))
      | whnf (Us as (Lam _, s)) = Us
      | whnf (EVar (ref (SOME U), _, _), s) = whnf (U, s)
      (* | whnf (Us as (EVar _, s)) = Us *)
      (* next two avoid calls to whnf (V, id), where V is type of X *)
      | whnf (Us as (EVar (r, Root _, _), s)) = Us 
      | whnf (Us as (EVar (r, Uni _, _), s)) = Us 
      | whnf (Us as (X as EVar (r, V, _), s)) = 
          (case whnf (V, id)
	     of (Pi _, _) => (lower X; whnf Us)
	      | _ => Us)
      | whnf (EClo (U, s'), s) = whnf (U, comp (s', s)) 

    (* expandDef (Root (Def (d), S), s) = (U' ,s')
     
       Invariant:
       If    G |- s : G1     G1 |- S : V > W            ((d @ S), s) in whnf
                             .  |- d = U : V'  
       then  G |- s' : G'    G' |- U' : W'
       and   G |- V' == V [s] : L
       and   G |- W' [s'] == W [s] == W'' : L
       and   G |- (U @ S) [s] == U' [s'] : W'
       and   (U', s') in whnf
    *)
    fun expandDef (Root (Def (d), S), s) = 
	  whnfRedex (whnf (constDef (d), id), (S, s))

    (* inferSpine ((S, s1), (V, s2)) = (V', s')

       Invariant:
       If  G |- s1 : G1  and  G1 |- S : V1 > V1'
       and G |- s2 : G2  and  G2 |- V : L,  (V, s2) in whnf
       and G |- S[s1] : V[s2] > W  (so V1[s1] == V[s2] and V1[s1] == W)
       then G |- V'[s'] = W
    *)
    fun inferSpine ((Nil, _), Vs) = Vs
      | inferSpine ((SClo (S, s'), s), Vs) = 
          inferSpine ((S, comp (s', s)), Vs)
      | inferSpine ((App (U, S), s1), (Pi ((Dec (_, V1), _), V2), s2)) =
	  inferSpine ((S, s1), whnf (V2, Dot (Exp (EClo (U, s1), V1), s2)))

    (* inferCon (C) = V  if C = c or C = d and |- C : V *)
    fun inferCon (Const (cid)) = constType (cid)
      | inferCon (Def (cid)) = constType (cid)

    (* etaExpand' (U, (V,s)) = U'
           
       Invariant : 
       If    G |- U : V [s]   (V,s) in whnf
       then  G |- U' : V [s]
       and   G |- U == U' : V[s]
       and   (U', id) in whnf and U' in head-eta-long form
    *)
    (* quite inefficient -cs *)
    fun etaExpand' (U, (Root _, s)) = U
      | etaExpand' (U, (Pi ((D, _), V), s)) =
          Lam (decSub (D, s), 
	       etaExpand' (Redex (EClo (U, shift), 
				  App (Root (BVar (1), Nil), Nil)), whnf (V, dot1 s)))

    (* etaExpandRoot (Root(H, S)) = U' where H = c or H = d

       Invariant:
       If   G |- H @ S : V  where H = c or H = d
       then G |- U' : V
       and  G |- H @ S == U'
       and (U',id) in whnf and U' in head-eta-long form
    *)
    fun etaExpandRoot (U as Root(H, S)) =
          etaExpand' (U, inferSpine ((S, id), (inferCon(H), id)))

    (* whnfEta ((U, s1), (V, s2)) = ((U', s1'), (V', s2)')
     
       Invariant:
       If   G |- s1 : G1  G1 |- U : V1
       and  G |- s2 : G2  G2 |- V : L
       and  G |- V1[s1] == V[s2] : L

       then G |- s1' : G1'  G1' |- U' : V1'
       and  G |- s2' : G2'  G2' |- V' : L'
       and  G |- V1'[s1'] == V'[s2'] : L
       and (U', s1') is in whnf
       and (V', s2') is in whnf
       and (U', s1') == Lam x.U'' if V[s2] == Pi x.V''

       Similar to etaExpand', but without recursive expansion
    *)
    fun whnfEta (Us, Vs) = whnfEtaW (whnf Us, whnf Vs)

    and whnfEtaW (UsVs as (_, (Root _, _))) = UsVs
      | whnfEtaW (UsVs as ((Lam _, _), (Pi _, _))) = UsVs
      | whnfEtaW ((U, s1), Vs2 as (Pi ((D, P), V), s2)) =
          ((Lam (decSub (D, s2), 
		 Redex (EClo (U, comp (s1, shift)), 
			App (Root (BVar (1), Nil), Nil))), id), Vs2)

    (* Invariant:
     
       normalizeExp (U, s) = U'
       If   G |- s : G' and G' |- U : V 
       then U [s] = U'
       and  U' in existential normal form

       If (U, s) contain no existential variables,
       then U' in normal formal
    *)
    fun normalizeExp Us = normalizeExpW (whnf Us)

    and normalizeExpW (U as Uni (L), s) = U
      | normalizeExpW (Pi (DP, U), s) = 
          Pi (normalizeDecP (DP, s), normalizeExp (U, dot1 s))
      | normalizeExpW (U as Root (H, S), s) = (* s = id *)
	  Root (H, normalizeSpine (S, s))
      | normalizeExpW (Lam (D, U), s) = 
	  Lam (normalizeDec (D, s), normalizeExp (U, dot1 s))
      | normalizeExpW (Us as (EVar _, s)) = EClo Us 

    and normalizeSpine (Nil, s) = 
          Nil 
      | normalizeSpine (App (U, S), s) = 
          App (normalizeExp (U, s), normalizeSpine (S, s))
      | normalizeSpine (SClo (S, s'), s) =
	  normalizeSpine (S, comp (s', s))

    and normalizeDec (Dec (xOpt, V), s) = Dec (xOpt, normalizeExp (V, s))
    and normalizeDecP ((D, P), s) = (normalizeDec (D, s), P)

    (* dead code -fp *)
    (* pre-Twelf 1.2 code walk Fri May  8 11:37:18 1998 *)
    (*
    and normalizeSub (s as Shift _) = s
      | normalizeSub (Dot (Ft as Idx _, s)) =
	  Dot (Ft, normalizeSub (s))
      | normalizeSub (Dot (Exp (U, V), s)) =
	  Dot (Exp (normalizeExp (U, id), normalizeExp (V, id)),
		 normalizeSub s)
    *)

    fun normalizeCtx Null = Null
      | normalizeCtx (Decl (G, D)) = 
          Decl (normalizeCtx G, normalizeDec (D, id))

  in
    val whnf = whnf
    val expandDef = expandDef
    val etaExpandRoot = etaExpandRoot
    val whnfEta = whnfEta

    val normalize = normalizeExp
    val normalizeDec = normalizeDec
    val normalizeCtx = normalizeCtx
  end
end;  (* functor Whnf *)
