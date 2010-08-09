structure SortRecon :> SORTRECON =
  struct
    structure I = IntSyn

    (*
    Basic algorithm on terms.  Backtracking is done purely locally using
    short-circuiting boolean || and passing along the atomic sort we are
    ultimately checking at.

    check : ctx -> tm -> sort -> bool

    check(Γ ⊦ N : ⊤) = true
    check(Γ ⊦ N : S1 ∧ S2) = check(Γ ⊦ N : S1) && check(Γ ⊦ N : S2)
    check(Γ ⊦ λ x. N : Π x:S1. S2) = check(Γ, x:S1 ⊦ N : S2)
    check(Γ ⊦ x ⋅ Sp : Q) = split(Γ ⊦ Sp : Γ(x) < Q)

    split : ctx -> spine -> sort -> asort -> bool

    split(Γ ⊦ Sp : ⊤ < Q) = false
    split(Γ ⊦ Sp : S1 ∧ S2 < Q) = split(Γ ⊦ Sp : S1 < Q)
                               || split(Γ ⊦ Sp : S2 < Q)
    split(Γ ⊦ () : Q' < Q) = Q' ≤ Q
    split(Γ ⊦ (M; Sp) : Π x:S1. S2 < Q) = split(Γ ⊦ Sp : [M/x]S2 < Q)
                                       && check(Γ ⊦ M : S1)
                                       (* reversed order means we don't
                                          bother checking arguments until
                                          we know the head can succeed *)
    *)

  datatype constraint =
      True
    | And of constraint * constraint
    | False
    | Or of constraint * constraint
    | Subsort of I.Exp * I.Exp
    | Check of I.dctx * I.Exp * I.Exp

  fun ctxDec (G, k) =
      let (* ctxDec' (G'', k') = x:V
             where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
        fun ctxDec' (I.Decl (G', I.Dec (x, V')), 1) = I.Dec (x, V')
          | ctxDec' (I.Decl (G', _), k') = ctxDec' (G', k'-1)
         (* ctxDec' (Null, k')  should not occur by invariant *)
      in
        ctxDec' (G, k)
      end

    fun lookup (G, I.BVar k) =
            let val I.Dec (_, V) = ctxDec (G, k)
            in
                [V]
            end
      | lookup (G, I.Const c) = Refinements.refinements c

    (* [check (G, U, V)] iff G |- U <= V.
       assumes: U is normal and G and V are well-formed *)
    fun check (G, U, V) =
        (* first, try checking a term at an intersection sort *)
        case Sorts.view V of
            Sorts.Top => true
          | Sorts.Inter (S1, S2) => check (G, U, S1)
                            andalso check (G, U, S2)
          (* XXX stopgap just for testing -- shouldn't really accept this *)
          | Sorts.Unknown => true
          | Sorts.Basic V (* shadow *) =>
                (* then, try checking an intersection sort at a class *)
                case Sorts.view U of
                    Sorts.Top => true
                  | Sorts.Inter (S1, S2) => check (G, S1, V)
                                    andalso check (G, S2, V)
                  (* otherwise, just check term/sort at sort/class *)
                  | Sorts.Basic U (* shadow *) => check' (G, U, V)
                  (* XXX stopgap just for testing -- shouldn't really accept this *)
                  | Sorts.Unknown => true

    (* [check' (G, U, V)] iff G |- U <= V.
       invariant: U and V are basic (neither intersection nor top) *)
    and (* check' (G, I.EClo (U, _), V) = check' (G, U, V)
      | check' (G, U, I.EClo (V, _)) = check' (G, U, V)
        (* λ x. N <= Π x:S1. S2 if x:S1 ⊦ N <= S2 *)
      | *)
        check' (G, I.Lam (_, M), I.Pi ((D, _), S2)) =
            check (I.Decl (G, D), M, S2)
        (* h ⋅ Sp <= Q if Sp : lookup(h) < Q *)
      | check' (G, I.Root (h, Sp), I.Root (I.Const q, _)) =
            split (G, Sp, lookup(G, h), SOME q)
            (* NB: don't care about checking indices, only heads:
               refinement restriction already verified at this point *)
        (* q ⋅ Sp <= sort if Sp : lookup(h) < sort *)
      | check' (G, I.Root (h, Sp), I.Uni I.Sort) =
            split (G, Sp, lookup(G, h), NONE)
        (* Π x:S1. S2 <= L if S1 <= sort and x:S1 ⊦ S2 <= L *)
      | check' (G, I.Pi ((D as I.Dec (y, S1), _), S2), I.Uni L) =
            check (G, S1, I.Uni I.Sort) andalso
            check (I.Decl (G, D), S2, I.Uni L)
        (* sort <= class *)
      | check' (G, I.Uni I.Sort, I.Uni I.Class) = true

    (* [split (G, Sp, Vs, SOME q)]  iff G |- Sp : /\(Vs) < q ⋅ _, or
       [split (G, Sp, Vs, NONE)]    iff G |- Sp : /\(Vs) < sort *)
    and split (G, Sp, [], _) = false
      | split (G, Sp, V::Vs, qo) =
        case Sorts.view V of
            Sorts.Top => split (G, Sp, Vs, qo)
          | Sorts.Inter (V1, V2) => split (G, Sp, V1::V2::Vs, qo)
          | Sorts.Basic V => split' (G, Sp, V, qo) orelse split (G, Sp, Vs, qo)
          (* XXX stopgap for testing -- shouldn't really accept this *)
          | Sorts.Unknown => true

    (* [split' (G, Sp, V, SOME q)]  iff G |- Sp : V < q ⋅ _, or
       [split' (G, Sp, V, NONE)]    iff G |- Sp : V < sort.
       invariant: V is basic (neither intersection nor top) *)
    and (* split' (G, I.SClo (Sp, _), V, qo) = split' (G, Sp, V, qo)
      | split' (G, Sp, I.EClo (V, _), qo) = split' (G, Sp, V, qo)
      | *)
        split' (G, I.Nil, I.Root (I.Const q', _), SOME q) = Subsort.subsort q' q
      | split' (G, I.Nil, I.EClo _, SOME q) = (print "ARGH...\n"; raise Match)
      | split' (G, I.Nil, I.Uni I.Sort, NONE) = true
      | split' (G, I.App (M, Sp), I.Pi ((I.Dec (y, S1), _), S2), qo) =
            split (G, Sp, [S2], qo) andalso check (G, M, S1)
            (* NB: don't bother doing substitution, c.f. refinement restr. *)
      | split' (G, Sp, S, qo) =
            (print "*** DEBUG: \n    ";
             print (Print.ctxToString (IntSyn.Null, G));
             print " |- ";
             print (Print.spineToString (G, Sp));
             print " : ";
             print (Print.expToString (G, S));
             print " < ";
             print (case qo of NONE => "sort"
                             | SOME q => IntSyn.constName q);
             print "\n";
             raise Match)
  end
