(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

functor State 
  (structure Formatter : FORMATTER) : STATE =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure Formatter = Formatter

  datatype State
    = State of (Tomega.Dec IntSyn.Ctx * Tomega.For) * Tomega.Worlds

(*  datatype SideCondition  (* we need some work here *)
    = None
    | All   of SideCondition
    | And   of SideCondition * SideCondition
    | Order of Order.Predicate
*)

  exception Error of string

  local 
    structure T = Tomega
    structure I = IntSyn
    (* init F = S

       Invariant:
       S = (. |> F) is the initial state
    *)
    fun init (F, W) = State ((I.Null, F), W)

    (* close S = B

       Invariant:
       If   S = (Psi |> F) state 
       and  F == F'
       then B = true 
       else B = false
    *)
    fun close (State ((_, F), _)) = 
         T.convFor ((T.forSub (F, T.id), T.id), (T.True, T.id))

    fun construct (State ((Psi, T.And (F1, F2)), W)) sc fc =
          construct (State ((Psi, F1), W)) 
	    (fn P1 => construct (State ((Psi, F2), W))
	                (fn P2 => sc (T.PairPrg (P1, P2)))
			fc)
	    fc
      | construct (State ((Psi, T.True), W)) sc fc =
	  sc (T.Unit)
      | construct (State ((Psi, T.All ((D, _), F)), W)) sc fc =
	  construct (State ((I.Decl (Psi, D), F), W)) sc fc
	  
      
  in
    val close = close
    val init = init
    val construct = construct
  end
end