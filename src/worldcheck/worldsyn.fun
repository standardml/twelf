(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)

functor WorldSyn (structure IntSyn : INTSYN
		  structure Whnf : WHNF
		    sharing Whnf.IntSyn = IntSyn
	          structure Index : INDEX
		    sharing Index.IntSyn = IntSyn
		  structure Names : NAMES
		    sharing Names.IntSyn = IntSyn
		  structure Unify : UNIFY
		    sharing Unify.IntSyn = IntSyn
		  structure CSManager : CS_MANAGER
		    sharing CSManager.IntSyn = IntSyn) : WORLDSYN= 
struct
  structure IntSyn = IntSyn
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

    datatype Reg			(* Regular world expressions  *)
      = Block of LabelDec		(* R ::= LD                   *)
      | Star of Reg			(*     | R*                   *)
      | Plus of Reg * Reg		(*     | R1 + R2              *)
      | One				(*     | 1                    *)

    exception Success			(* signals worldcheck success *)

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

    
    (* shift S = S'

       Invariant:
       If    S = ((t1, L1) .... (tn, Ln))
       and   G |- ti : Gi
       and   Gi |- Li ctx
       then  S = ((t1', L1) .... (tn', Ln))
       where   G, V |- ti' : Gi
    *)
    fun shift S = map (fn (t', L') => (I.comp (t', I.shift), L')) S 

    (* empty S = ()
  
       Invariant:
       empty S terminates with () (failure) 
       iff  (t,L) in S with L <> []
       Side effect:  Exception Success is raised
    *)
    fun empty nil = raise Success
      | empty ((_, nil) :: L) = empty L
      | empty _ = ()

    (* init (G, V, S) = ()
      
       Invariant:  (Initial continuation)
       Let  G |- V : K
       init (G, V, S) terminates with () (failure) 
       iff V is not atomic, or there exists (t,L) in S with L <> []
       Side effect:  Exception Success is raised
    *)
    fun init (_, I.Root _, S) = empty S
      | init _ = ()


    (* accR (G, V, S) R k = ()
  
       Invariant:
       If   G |- V : K
       and  G |- S : list of declarations under substitutions
       and  R is a regular expression 
       and  k a continuation that expects (G, V, S) as argument
       accR (G, V, S) R k teriminate with () (failure)
       iff V does not match S and R
       Side effect:  Exception Success is raised
    *)
    fun accR GVS One k =
          (k GVS; accR' GVS (fn GVS' => accR GVS' One k))
      | accR (GVS as (G, V as I.Pi ((D as I.Dec (_, V11), _), V12), S))
	  (Block (LabelDec (_, L1, I.Dec (_, V2) :: L2))) k =
	  let 
	    val t = createEVarSub (G, L1)	(* G |- t : L1 *)
	  in
	    (CSManager.trail (fn () => (Unify.unify (G, (V11, I.id), (V2, t)); 
	     accR (I.Decl (G, D), V12, (I.dot1 t, L2) :: shift S) One k)
	    handle Unify.Unify _ => ());
	     accR' GVS (fn GVS' => accR GVS' One k))
	  end
      | accR (G, I.Root _, S) (Block _) k = ()
      | accR GVS (Plus (r1, r2)) k = 
	  (accR GVS r1 k; accR GVS r2 k)
      | accR GVS (r' as (Star r)) k =
	  (k GVS; accR GVS r (fn GVS' => accR GVS' r' k))   
					(* terminates because the regular 
					   expression that denotes the 
					   regular word does not contain
					   the empty word    --cs *)


    (* accR' (G, V, S) k = ()
  
       Invariant:
       If   G |- V : K
       and  G |- S : list of declarations under substitutions
       and  k a continuation that expects (G, V, S) as argument
       accR' (G, V, S) k teriminate with () (failure)
       iff V is atomic 
           or V = {x:V1}V'  
              and there is no block (t, V2 :: L) in S
	          with  G |- t : G' and G' |- L ctx
              s.t. V, and V2[t] are not unifable

       Side effect:  Exception Success is raised
    *)
    and accR' (_, _, nil) k = ()
      | accR' (_, I.Root _, _) k = ()
      | accR' (G, V as I.Pi ((D as I.Dec (_, V11), _), V12),
		((t, L2 as I.Dec (_, V2) :: L2') :: S1)) k =
          (CSManager.trail (fn () => (Unify.unify (G, (V11, I.id), (V2, t)); 
	    k (I.Decl (G, D), V12, (I.dot1 t, L2') :: shift S1))
	   handle Unify.Unify _ => ());
	   accR' (G, V, S1) (fn (G', V', S') => 
              k (G', V', (I.comp (t, I.shift), L2) :: S')))
      | accR' (G, V, ((_,[]) :: S1)) k = accR' (G, V, S1) k
	    

    (* ctxtolist G = L
      
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


    (* worldToReg W = R
  
       Invariant:
       W = R, except that R is a regular expression 
       with non-empty contextblocks as leaves
    *)
    fun worldToReg W = 
      let
	fun worldToReg' (Closed) = One
	  | worldToReg' (Schema (Closed, L)) = Block L
	  | worldToReg' (Schema (W, L)) = Plus (worldToReg' W, Block L)
      in
	Star (worldToReg' W)
      end

    (* worldToReg W (G, V) = ()
  
       Invariant:
       If   G |- V : K
       and  W world
       then worldReg W (G, V) terminates with ()  (success)
	    iff all leading abstractions G, can be completely
	    covered by blocks declared in W
    *)
    fun checkBlocks W (G, V) = 
      (accR (G, V, []) (worldToReg W) init;
       raise Error "World violation") handle Success => ()


    (* worldcheck W a = ()

       Invariant:       
       Let {A1 ... An} all normal forms of types of type family a
       worldcheck W a terminates with ()
       iff  . |-+ Ai
    *) 
    fun worldcheck W a =  
      let
	(* checkPos (G, V) = ()

  	   Invariant:
	   If   G is a context
           and  G |- V : K       (V is in normal form)
           then checkPos (G, V) terminates with () iff G |-(+) V
	     (see regularworlds.tex for the rules)
	*)
	fun checkPos (G, I.Root (a, S)) = ()
	  | checkPos (G, I.Pi ((D as I.Dec (_, V1), I.Maybe), V2)) = 
	    (checkPos (I.Decl (G, D), V2);
	     checkNeg (G, V1))
	  | checkPos (G, I.Pi ((D as I.Dec (_, V1), I.No), V2)) = 
	    (checkBlocks W (G, V1);
	     checkPos (I.Decl (G, D), V2);
	     checkNeg (G, V1))

        (* checkNeg (G, V) = () 

           Invariant:
           If   G is a context
           and  G |- V : K
           then checkNeg (G, V) terminates with () iff  G |-(-) V
           (see regularworlds.tex for the rules)
        *)
	
	and checkNeg (G, I.Root (a, S)) = ()
	  | checkNeg (G, I.Pi ((D as I.Dec (_, V1), _), V2)) =
              (checkNeg (I.Decl (G, D), V2) ;
	       checkPos (G, V1))
	
	fun checkAll nil = ()
	  | checkAll (I.Const a :: alist) =
	      (if (!Global.chatter) > 4 then 
		 TextIO.print ("[" ^ Names.constName a) else ();
	       checkPos (I.Null, I.constType a);
	       if (!Global.chatter) > 4 then 
		   TextIO.print ("]\n") else ();
	       checkAll alist)
      in
	checkAll (Index.lookup a)
      end

  in
    val worldcheck = worldcheck
    val ctxToList = ctxToList
  end


end (* functor WorldSyn *)
