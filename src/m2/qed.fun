(* QED *)
(* Author: Carsten Schuermann *)

functor Qed (structure Global : GLOBAL
             structure MetaSyn' : METASYN)
  : QED =
struct
  structure MetaSyn = MetaSyn'

  exception Error of string

  local
    structure M = MetaSyn
    structure I = IntSyn

    fun subgoal (M.State (name, M.Prefix (G, M, B), V)) =
        let
          fun check I.Null = true
            | check (I.Decl (M, M.Top)) = check M
            | check (I.Decl (M, M.Bot)) = false
        in
          check M
        end

  in
    val subgoal = subgoal
  end (* local *)
end; (* functor Qed *)
