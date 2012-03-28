(* Constraint Solver Manager *)
(* Author: Roberto Virga *)

functor CSManager (structure Global : GLOBAL
                   (*! structure IntSyn : INTSYN !*)
                   structure Unify : UNIFY
                   (*! sharing Unify.IntSyn = IntSyn !*)
                   structure Fixity : FIXITY
                   (*! structure ModeSyn : MODESYN !*))
  : CS_MANAGER =
struct
  structure IntSyn  = IntSyn
  structure Fixity  = Fixity
  (* structure ModeSyn = ModeSyn *)

  type sigEntry = (* global signature entry *)
    (* constant declaration plus optional precedence and mode information *)
    IntSyn.ConDec * Fixity.fixity option * ModeSyn.ModeSpine list

  type fgnConDec = (* foreign constant declaration *)
    {
      parse : string -> IntSyn.ConDec option
    }

  type solver = (* constraint solver *)
    {
      (* name is the name of the solver *)
      name : string,
      (* keywords identifying the type of solver *)
      (* NOTE: no two solvers with the same keywords may be active simultaneously *)
      keywords : string,
      (* names of other constraint solvers needed *)
      needs : string list,
      (* foreign constants declared (if any) *)
      fgnConst : fgnConDec option,
      (* install constants *)
      init : (int * (sigEntry -> IntSyn.cid)) -> unit,
      (* reset internal status *)
      reset : unit -> unit,
      (* trailing operations *)
      mark : unit -> unit,
      unwind : unit -> unit
    }

  exception Error of string

  local

    (* vacuous solver *)
    val emptySolver =
        {
          name = "",
          keywords = "",
          needs = nil,

          fgnConst = NONE,

          init = (fn _ => ()),

          reset = (fn () => ()),
          mark = (fn () => ()),
          unwind = (fn () => ())
        }

    (* Twelf unification as a constraint solver *)
    val unifySolver =
        {
          name = "Unify",
          keywords = "unification",
          needs = nil,

          fgnConst = NONE,

          init = (fn _ => ()),

          reset  = Unify.reset,
          mark   = Unify.mark,
          unwind = Unify.unwind
        }

    (* List of installed solvers *)

    datatype Solver = Solver of solver * bool ref

    val maxCS = Global.maxCSid
    val csArray = Array.array (maxCS+1, Solver (emptySolver, ref false)) : Solver Array.array
    val _ = Array.update (csArray, 0, Solver (unifySolver, ref true))
    val nextCS = ref(1) : int ref

    (* Installing function *)
    val installFN = ref (fn _ => ~1) : (sigEntry -> IntSyn.cid) ref
    fun setInstallFN f = (installFN := f)

    (* install the specified solver *)
    fun installSolver (solver) =
          let
            (* val _ = print ("Installing constraint domain " ^ #name solver ^ "\n") *)
            val cs = !nextCS
            val _ = if !nextCS > maxCS
                    then raise Error "too many constraint solvers"
                    else ()
            val _ = Array.update (csArray, cs, Solver (solver, ref false));
            val _ = nextCS := !nextCS+1
          in
            cs
          end

    (* install the unification solver *)
    val _ = installSolver (unifySolver)

    val activeKeywords = ref nil : string list ref

    (* make all the solvers inactive *)
    fun resetSolvers () =
          (
            ArraySlice.appi (fn (cs, Solver (solver, active)) =>
                                if !active then
                                    (
                                     active := false;
                                     #reset(solver) ()
                                    )
                                else ())
                            (ArraySlice.slice (csArray, 0, SOME(!nextCS)));
            activeKeywords := nil;
            useSolver "Unify"
          )

    (* make the specified solver active *)
    and useSolver name =
          let
            exception Found of IntSyn.csid
            fun findSolver name =
                  (
                    ArraySlice.appi (fn (cs, Solver (solver, _)) =>
                                        if (#name(solver) = name)
                                        then raise Found cs
                                        else ())
                                    (ArraySlice.slice (csArray, 0, SOME(!nextCS)));
                    NONE
                  ) handle Found cs => SOME(cs)
          in
            case findSolver name
              of SOME(cs) =>
                   let
                     val Solver (solver, active) = Array.sub (csArray, cs)
                   in
                     if !active then ()
                     else if List.exists (fn s => s = #keywords(solver))
                                         (!activeKeywords)
                     then raise Error ("solver " ^ name ^
                                       " is incompatible with a currently active solver")
                     else
                       (
                          active := true;
                          activeKeywords := #keywords(solver) :: (!activeKeywords);
                          List.app useSolver (#needs(solver));
                          #init(solver) (cs, !installFN)
                       )
                   end
               | NONE => raise Error ("solver " ^ name ^ " not found")
          end

  (* ask each active solver to try and parse the given string *)
  fun parse string =
        let
          exception Parsed of IntSyn.csid * IntSyn.ConDec
          fun parse' (cs, solver : solver) =
                (case #fgnConst(solver)
                           of NONE => ()
                            | SOME(fgnConDec) =>
                                (case #parse(fgnConDec) (string)
                                   of NONE => ()
                                    | SOME conDec => raise Parsed (cs, conDec)))
        in
          (
            ArraySlice.appi (fn (cs, Solver (solver, active)) =>
                                if !active then parse' (cs, solver) else ())
                            (ArraySlice.slice (csArray, 0, SOME(!nextCS)));
            NONE
          ) handle Parsed info => SOME(info)
        end


  val markCount = ref 0 : int ref

  (* reset the internal status of all the active solvers *)
  fun reset () =
        ArraySlice.appi (fn (_, Solver (solver, active)) =>
                            if !active then (markCount := 0; #reset(solver) ())
                            else ())
                        (ArraySlice.slice (csArray, 0, SOME(!nextCS)));


  (* mark all active solvers *)
  fun mark () =
        (markCount := !markCount + 1;
          ArraySlice.appi (fn (_, Solver (solver, active)) =>
                              if !active then #mark(solver) () else ())
                          (ArraySlice.slice (csArray, 0, SOME(!nextCS))))

  (* unwind all active solvers *)
  fun unwind targetCount =
    let
      fun unwind' 0 = (markCount := targetCount)
        | unwind' k =
          (ArraySlice.appi (fn (_, Solver (solver, active)) =>
                               if !active then #unwind(solver) () else ())
           (ArraySlice.slice (csArray, 0, SOME(!nextCS)));
           unwind' (k-1))
    in
      unwind' (!markCount - targetCount)
    end


  (* trail the give function *)
  fun trail f =
        let
          val current = !markCount
          val _ = mark ()
          val r = f()
          val _ = unwind current
        in
          r
        end
  in
    val setInstallFN = setInstallFN

    val installSolver = installSolver
    val resetSolvers = resetSolvers
    val useSolver = useSolver

    val parse = parse

    val reset = reset
    val trail = trail
  end
end  (* functor CSManager *)

structure CSManager = CSManager (structure Global = Global
                                 (*! structure IntSyn = IntSyn !*)
                                 structure Unify = UnifyTrail
                                 structure Fixity = Names.Fixity
                                 (*! structure ModeSyn = ModeSyn !*));
