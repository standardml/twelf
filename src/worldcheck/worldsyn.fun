(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)

functor WorldSyn (structure IntSyn' : INTSYN
		  structure Whnf : WHNF
		    sharing Whnf.IntSyn = IntSyn'
	          structure Index : INDEX
		    sharing Index.IntSyn = IntSyn'
		  structure Unify : UNIFY
		    sharing Unify.IntSyn = IntSyn') : WORLDSYN= 
struct
  structure IntSyn = IntSyn'
  structure I = IntSyn

  exception Error of string 

  type label = int      
  type name = string
  type lemma = int 

  type dlist = IntSyn.Dec list

  datatype LabelDec =			(* ContextBody                *)
    LabelDec of name * dlist * dlist    (* LD = SOME G1. BLOCK G2     *)

  datatype World =			(* Worlds                     *)
    Closed				(* W ::= .                    *)
  | Schema of World * LabelDec          (*     | W, l : LD            *)

  local
    (* ctxToList G = L
      
       Invariant:
       G = L  (G is left associative, L is right associative)
    *)
    fun ctxToList (Gin) = 
      let
	fun ctxToList' (I.Null, G ) = G
	  | ctxToList' (I.Decl (G, D), G') =
	  ctxToList' (G, D :: G')
      in
	ctxToList' (Gin, nil)
      end

    (* createEVarSub G L = s
     
       Invariant:
       If   G is a context
       and  L is a context
       then G |- s : L
    *)
    fun createEVarSub (G, nil) = I.Shift (I.ctxLength G)
      | createEVarSub (G, (I.Dec (_, V) :: L)) = 
        let
	  val s = createEVarSub (G, L)
	  val V' = I.EClo (V, s)
	  val X = I.newEVar (G, V')
	in
          I.Dot (I.Exp X, s)
	end


    (* worldcheck W a = ()

       Invariant:       
       Let {A1 ... An} all normal forms of types of type family a
       worldcheck W a terminates with ()
       iff  . |-+ Ai
    *) 
    fun worldcheck W a =  
      let

	(* checkPos W (G, (V, s)) = ()

  	   Invariant:
	   If   G is a context
           and  G |- s : G'
           and  G' |- V : K
           then checkPos W (G, (V, s)) terminates with () iff G |-+ B[s]
	     (see regularworlds.tex for the rules)
	*)
	fun checkPos W' (G, (I.Root (a, S), s)) = ()
	  | checkPos Closed (G, (I.Pi ((I.Dec (_, V1), _), V2), s)) = 
	  raise Error "Incompatible worlds"
	  | checkPos (Schema (W', LabelDec (_, L1, L2))) (Gus as (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s))) = 
	    ((let
		val t = createEVarSub (G, L1)	(* G |- s' : L1 *)
	      in
		(checkNeg W (G, (L2, t), (V1, s)) ;
		 checkPos W' (I.Decl (G, I.decSub (D, s)), (V2, I.dot1 s)))
	      end) handle Unify.Unify _ => checkPos W' Gus)
	and checkPosW W' (G, Us) = checkPos W' (G, Whnf.whnf Us)

        (* checkNeg W (G, (L, t), (V, s)) = () 

           Invariant:
           If   G is a context
           and  G |- t : G1
           and  G1 |- L  context
           and  G |- s : G2
           and  G |- V : K
           then checkNeg W (G, (L, t), (V, s)) terminates with () iff  G |-- [t] L ~ V [s]
           (see regularworlds.tex for the rules)
        *)
        and checkNeg W' (G, (L, t), (I.Root (a, S), s)) = ()
          | checkNeg W' (G, (I.Dec (_, V) :: L, t), (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =
	  let 
	    val _ = Unify.unify (G, (V, t), (V1, s))
	  in
	    (checkNeg W' (I.Decl (G, I.decSub (D, s)), (L, t), (V2, I.dot1 s)) ;
	     checkPos W (G, (V1, s)))
	  end
	
	fun checkTopLevel W' (G, (I.Root (a, S), s)) = ()
	  | checkTopLevel W' (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =
              (checkTopLevel W' (I.Decl (G, I.decSub (D, s)), (V2, I.dot1 s)) ;
	       checkPos W (G, (V1, s)))
	
	fun checkAll nil = ()
	  | checkAll (I.Const a :: alist) =
	      (checkTopLevel W (I.Null, (I.constType a, I.id));
	       checkAll alist)
      in
	checkAll (Index.lookup a)
      end

  in
    val worldcheck = worldcheck
    val ctxToList = ctxToList
  end


end (* functor WorldSyn *)
