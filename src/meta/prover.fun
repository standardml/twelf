(* Meta Theorem Prover Version 1.3 *)
(* Author: Carsten Schuermann *)

functor MTProver (structure MTPGlobal : MTPGLOBAL
                  (*! structure IntSyn' : INTSYN !*)
                  (*! structure FunSyn : FUNSYN !*)
                  (*! sharing FunSyn.IntSyn = IntSyn' !*)
                  structure StateSyn : STATESYN
                  (*! sharing IntSyn = IntSyn' !*)
                  (*! sharing StateSyn.FunSyn = FunSyn !*)
                  structure Order : ORDER
                  (*! sharing Order.IntSyn = IntSyn' !*)
                  structure MTPInit : MTPINIT
                  (*! sharing MTPInit.FunSyn = FunSyn !*)
                    sharing MTPInit.StateSyn = StateSyn
                  structure MTPStrategy : MTPSTRATEGY
                    sharing MTPStrategy.StateSyn = StateSyn
                  structure RelFun : RELFUN
                  (*! sharing RelFun.FunSyn = FunSyn !*)
                      )
  : PROVER =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  local
    structure I = IntSyn
    structure F = FunSyn
    structure S = StateSyn

    (* DISCLAIMER: This functor is temporary. Its purpose is to
       connect the new prover to Twelf  (see also functor below) *)

    (* List of open states *)
    val openStates : S.State list ref = ref nil

    (* List of solved states *)
    val solvedStates : S.State list ref = ref nil

    fun transformOrder' (G, Order.Arg k) =
        let
          val k' = (I.ctxLength G) -k+1
          val I.Dec (_, V) = I.ctxDec (G, k')
        in
          S.Arg ((I.Root (I.BVar k', I.Nil), I.id), (V, I.id))
        end
      | transformOrder' (G, Order.Lex Os) =
          S.Lex (map (fn O => transformOrder' (G, O)) Os)
      | transformOrder' (G, Order.Simul Os) =
          S.Simul (map (fn O => transformOrder' (G, O)) Os)

    fun transformOrder (G, F.All (F.Prim D, F), Os) =
          S.All (D, transformOrder (I.Decl (G, D), F, Os))
      | transformOrder (G, F.And (F1, F2), O :: Os) =
          S.And (transformOrder (G, F1, [O]),
                 transformOrder (G, F2, Os))
      | transformOrder (G, F.Ex _, [O]) = transformOrder' (G, O)
      | transformOrder (G, F.True, [O]) = transformOrder' (G, O)
        (* last case: no existentials---order must be trivial *)

    fun select c = (Order.selLookup c handle _ => Order.Lex [])

    fun error s = raise Error s

    (* reset () = ()

       Invariant:
       Resets the internal state of open states/solved states
    *)
    fun reset () =
        (openStates := nil;
         solvedStates := nil)

    (* contains (L1, L2) = B'

       Invariant:
       B' holds iff L1 subset of L2 (modulo permutation)
    *)
    fun contains (nil, _) = true
      | contains (x :: L, L') =
          (List.exists (fn x' => x = x') L') andalso contains (L, L')

    (* equiv (L1, L2) = B'

       Invariant:
       B' holds iff L1 is equivalent to L2 (modulo permutation)
    *)
    fun equiv (L1, L2) =
          contains (L1, L2) andalso contains (L2, L1)

    (* insertState S = ()

       Invariant:
       If S is successful prove state, S is stored in solvedStates
       else S is stored in openStates
    *)
    fun insertState S =
        openStates := S :: (! openStates)


    (* cLtoString L = s

       Invariant:
       If   L is a list of cid,
       then s is a string, listing their names
    *)
    fun cLToString (nil) = ""
      | cLToString (c :: nil) =
          (I.conDecName (I.sgnLookup c))
      | cLToString (c :: L) =
          (I.conDecName (I.sgnLookup c)) ^ ", " ^ (cLToString L)

    (* init (k, cL) = ()

       Invariant:
       If   k is the maximal search depth
       and  cL is a complete and consistent list of cids
       then init initializes the openStates/solvedStates
       else an Error exception is raised
    *)
    fun init (k, cL as (c :: _)) =
        let
          val _ = MTPGlobal.maxFill := k
          val _ = reset ();
          val cL' = Order.closure c
                    handle Order.Error _ => cL  (* if no termination ordering given! *)
          val F = RelFun.convertFor cL
          val O = transformOrder (I.Null, F, map select cL)

        in
          if equiv (cL, cL')
            then List.app (fn S => insertState S) (MTPInit.init (F, O))
          else raise Error ("Theorem by simultaneous induction not correctly stated:"
                             ^ "\n            expected: " ^ (cLToString cL'))
        end

    (* auto () = ()

       Invariant:
       Solves as many States in openStates
       as possible.
    *)
    fun auto () =
        let
          val (Open, solvedStates') = MTPStrategy.run (!openStates)
             handle Splitting.Error s => error ("Splitting Error: " ^ s)
                  | Filling.Error s => error ("Filling Error: " ^ s)
                  | Recursion.Error s => error ("Recursion Error: " ^ s)
                  | Filling.TimeOut =>  error ("A proof could not be found -- Exceeding Time Limit\n")

          val _ = openStates := Open
          val _ = solvedStates := (!solvedStates) @ solvedStates'
        in
          if (List.length (!openStates)) > 0 then
            raise Error ("A proof could not be found")
          else ()
        end


    fun print () = ()
    fun install _ = ()

  in
    val init = init
    val auto = auto
    val print = print
    val install = install
  end (* local *)
end (* functor MTProver *)



functor CombiProver (structure MTPGlobal : MTPGLOBAL
                     (*! structure IntSyn' : INTSYN !*)
                     structure ProverOld : PROVER
                     (*! sharing ProverOld.IntSyn = IntSyn' !*)
                     structure ProverNew : PROVER
                     (*! sharing ProverNew.IntSyn = IntSyn' !*)
                       )
  : PROVER =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  fun he f = f () handle ProverNew.Error s => raise Error s
                        | ProverOld.Error s => raise Error s

  local
    fun init Args =
      he (fn () => case !(MTPGlobal.prover)
                     of MTPGlobal.New => ProverNew.init Args
                      | MTPGlobal.Old => ProverOld.init Args)

    fun auto Args =
      he (fn () => case !(MTPGlobal.prover)
                        of MTPGlobal.New => ProverNew.auto Args
                         | MTPGlobal.Old => ProverOld.auto Args)

    fun print Args =
      he (fn () => case !(MTPGlobal.prover)
                        of MTPGlobal.New => ProverNew.print Args
                         | MTPGlobal.Old => ProverOld.print Args)

    fun install Args =
      he (fn () => case !(MTPGlobal.prover)
                        of MTPGlobal.New => ProverNew.install Args
                         | MTPGlobal.Old => ProverOld.install Args)
  in
    val init = init
    val auto = auto
    val print = print
    val install = install
  end (* local *)
end (* functor CombiProver *)
