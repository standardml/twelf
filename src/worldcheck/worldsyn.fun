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


    exception Success

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


    fun shift S = map (fn (t', L') => (I.comp (t', I.shift), L')) S 


    fun empty nil = raise Success
      | empty ((_, nil) :: L) = empty L
      | empty _ = ()

    fun init (_, I.Root _, S) = empty S
      | init _ = ()


    (* accR (G, V, S) R k = B
  
       Invariant:
       If   G |- V : K
       and  G |- S : list of Declarations
       and  R is a regular expression
       and  k a continuation that expects ((V, s), (S, t)) as argument
       then B holds iff V[s] matches S[t] and R.
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
	    

    (* -------------------------------------------------------------- *)

    

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


    (* checkBlock (G, (t, L), (V, s)) = () 
     
       Invariant:
       If   G is a context
       and  G |- t : G1
       and  G1 |- L  context
       and  G |- s : G2
       and  G2 |- V : K  (in normal form)
       then checkBlock (G, (t, L), (V, s)) terminates with () iff  G |-- [t] L ~ V [s]
       (see regularworlds.tex for the rules)
    *)
    fun checkBlock (G, (t, nil), I.Root (a, S)) = ()
      | checkBlock (G, (t, I.Dec (_, V) :: L), I.Pi ((D as I.Dec (_, V1), I.Maybe), V2)) =
        let 
	  val _ = Unify.unify (G, (V, t), (V1, I.id))
	in
	  checkBlock (I.Decl (G, D), (I.dot1 t, L), V2)
	end
      | checkBlock (G, (t, L), I.Pi ((D as I.Dec (_, V1), I.No), V2)) =
	  checkBlock (I.Decl (G, D), (I.comp (t, I.shift),  L), V2)
      | checkBlock _ = raise Error "World violation"

(*  (* checkBlocks W (G, (V, s)) = ()

       Invariant:
       If   G is a context
       and  G |- s : G'
       and  G' |- V : K
       then checkPos W (G, (V, s)) terminates with () 
	 iff there exists (SOME L1. BLOCK L2 \in W)
	 s.t. there exists a substituion   G |- t : L1
	 and G |- [t] L1 ~ V[s] 
	 (see regularworlds.tex for the rules)
    *)
    fun checkBlocks _ (G, I.Root _) = ()
      | checkBlocks Closed (G, V) = raise Error "World violation"
      | checkBlocks (Schema (W', LabelDec (_, L1, L2))) (GV as (G, V)) =
        ((let
	    val t = createEVarSub (G, L1)	(* G |- t : L1 *)
	  in
	    checkBlock (G, (t, L2), V)
	  end) handle Unify.Unify _ => checkBlocks W' GV)
*)


    fun worldToReg W = 
      let
	fun worldToReg' (Closed) = One
	  | worldToReg' (Schema (Closed, L)) = Block L
	  | worldToReg' (Schema (W, L)) = Plus (worldToReg' W, Block L)
      in
	Star (worldToReg' W)
      end

    fun checkBlocks W (G, V) = 
      (accR (G, V, []) (worldToReg W) init; raise Error "World violation") handle Success => ()


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
