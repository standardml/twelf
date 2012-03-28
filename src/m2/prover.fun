(* Meta Prover *)
(* Author: Carsten Schuermann *)

functor Prover (structure MetaGlobal : METAGLOBAL
                structure MetaSyn' : METASYN
                structure Init : INIT
                  sharing Init.MetaSyn = MetaSyn'
                structure Strategy : STRATEGY
                  sharing Strategy.MetaSyn = MetaSyn'
                structure Filling : FILLING
                  sharing Filling.MetaSyn = MetaSyn'
                structure Splitting : SPLITTING
                  sharing Splitting.MetaSyn = MetaSyn'
                structure Recursion : RECURSION
                  sharing Recursion.MetaSyn = MetaSyn'
                structure Qed : QED
                  sharing Qed.MetaSyn = MetaSyn'
                structure MetaPrint : METAPRINT
                  sharing MetaPrint.MetaSyn = MetaSyn'
                structure Names : NAMES
                (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
                structure Timers : TIMERS)
  : PROVER =
struct
  (*! structure IntSyn = MetaSyn'.IntSyn !*)

  exception Error of string

  local
    structure MetaSyn = MetaSyn'
    structure M = MetaSyn
    structure I = IntSyn

    (* List of open states *)
    val openStates : MetaSyn.State list ref = ref nil

    (* List of solved states *)
    val solvedStates : MetaSyn.State list ref = ref nil



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
        if Qed.subgoal S then solvedStates := S :: (! solvedStates)
        else openStates := S :: (! openStates)


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
          val _ = MetaGlobal.maxFill := k
          val _ = reset ();
          val cL' = Order.closure c
                    handle Order.Error _ => cL  (* if no termination ordering given! *)
        in
          if equiv (cL, cL')
            then List.app (fn S => insertState S) (Init.init cL)
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
          val _ = print "M2.Prover.auto\n"
          val (Open, solvedStates') = Strategy.run (!openStates)
             handle Splitting.Error s => error ("Splitting Error: " ^ s)
                  | Filling.Error s => error ("A proof could not be found -- Filling Error: " ^ s)
                  | Recursion.Error s => error ("Recursion Error: " ^ s)
                  | Filling.TimeOut =>  error ("A proof could not be found -- Exceeding Time Limit\n")

          val _ = openStates := Open
          val _ = solvedStates := (!solvedStates) @ solvedStates'
        in
          if (List.length (!openStates)) > 0 then
            raise Error ("A proof could not be found")
          else ()
        end

    (* makeConDec (name, (G, M), V) = e'

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V : type
       then e' = (name, |G|, {G}.V, Type) is a signature conDec
    *)
    fun makeConDec (M.State (name, M.Prefix (G, M, B), V)) =
        let
          fun makeConDec' (I.Null, V, k) = I.ConDec (name, NONE, k, I.Normal, V, I.Type)
            | makeConDec' (I.Decl (G, D), V, k) =
              makeConDec' (G, I.Pi ((D, I.Maybe), V), k+1)
        in
          (makeConDec' (G, V, 0))
        end

    (* makeSignature (SL) = IS'

       Invariant:
       If   SL is a list of states,
       then IS' is the corresponding interface signaure
    *)
    fun makeSignature (nil) = M.SgnEmpty
      | makeSignature (S :: SL) =
          M.ConDec (makeConDec S,
                      makeSignature SL)

    (* install () = ()

       Invariant:
       Installs solved states into the global signature.
    *)
    fun install (installConDec) =
        let
          fun install' M.SgnEmpty = ()
            | install' (M.ConDec (e, S)) =
                (installConDec e;
                 install' S)
          val IS = if (List.length (!openStates)) > 0 then
                     raise Error ("Theorem not proven")
                   else makeSignature (!solvedStates)
        in
          (install' IS;
           if !Global.chatter > 2 then
             (print "% ------------------\n";
              print (MetaPrint.sgnToString (IS));
              print "% ------------------\n")
           else ())
        end

    (* print () = ()

       Invariant:
       Prints the list of open States and the list of closed states.
    *)
    fun printState () =
        let
          fun print' nil = ()
            | print' (S :: L) =
                (print (MetaPrint.stateToString S);
                 print' L)
        in
          (print "Open problems:\n";
           print "==============\n\n";
           print' (!openStates);
           print "Solved problems:\n";
           print "================\n\n";
           print' (!solvedStates))
        end

  in
    val print = printState
    val init = init
    val auto = auto
    val install = install
  end (* local *)
end; (* functor Prover *)
