(* Filling  Version 1.3*)
(* Author: Carsten Schuermann *)

functor MTPFilling (structure IntSyn : INTSYN
                    structure FunSyn : FUNSYN
		      sharing FunSyn.IntSyn = IntSyn
                    structure StateSyn' : STATESYN
		      sharing StateSyn'.FunSyn = FunSyn
		    structure Search   : MTPSEARCH
  		      sharing Search.StateSyn = StateSyn'
		    structure Whnf : WHNF
		      sharing Whnf.IntSyn = IntSyn)
  : MTPFILLING =
struct
  structure StateSyn = StateSyn'

  exception Error of string

  type operator = (unit -> bool)

  local
    structure S = StateSyn
    structure F = FunSyn
    structure I = IntSyn

    exception Success


    (* createEVars (G, M) = ((G', M'), s', GE')
      
       Invariant:

    *)
    fun createEVars (G, (F.True, s)) = (nil, F.Unit)
      | createEVars (G, (F.TClo (F, s'), s)) = 
          createEVars (G, (F, I.comp (s', s)))
      | createEVars (G, (F.Ex (I.Dec (_, V), F), s)) = 
	let 
	  val X = I.newEVar (G, I.EClo (V, s))
	  val X' = Whnf.lowerEVar X
	  val (Xs, P) = createEVars (G, (F, I.Dot (I.Exp X, s)))
	in
	  (X' :: Xs, F.Inx (X, P))
	end


    (* expand' ((G, M), V) = (OE', OL')

       Invariant:
    *)
    fun expand (S as S.State (n, (G, B), (IH, OH), d, O, H, R, F)) = 
	let 
	  val (Xs, P) = createEVars (G, (F, I.id))
	in
	  fn () => ((Search.searchEx (G, Xs, fn () => raise Success); false)
	            handle Success => true)
	end
    

    (* apply f = B'

    *)
    fun apply f = f ()

    fun menu _ =  "Filling   (closes this subgoal)" 
      
  in
    val expand = expand
    val apply = apply
    val menu = menu
  end (* local *)
end; (* functor Filling *)
