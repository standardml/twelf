
  (* -------------------------------------------------------------------------- *)
  (*  Printing                                                                  *)
  (* -------------------------------------------------------------------------- *)

  local   
    nonfix $ % & %%
    fun op$ x = Layout.str x
    fun op% x = Layout.mayAlign x
    fun op%% x = Layout.align x
    fun op& x = Layout.seq x
    fun paren x = &[$"(",x,$")"]
    fun bracket x = &[$"[",x,$"]"]
    fun squiggle x = &[$"{",x,$"}"]
    fun indent x = Layout.indent x
    fun uni_to_layout Type = $"type"
      | uni_to_layout Kind = $"kind"

    fun const_to_string sgn c = name(Sig.lookup sgn c)

    fun spine_to_list Nil = []
      | spine_to_list (App(E,S)) = E::spine_to_list S

    fun head_to_layout sgn (Const c) = $(const_to_string sgn c)
      | head_to_layout sgn (BVar n) = $(Int.toString n)

    fun needs_parens_in_arg_pos (Uni _) = false 
      | needs_parens_in_arg_pos (Root(_,Nil)) = false
      | needs_parens_in_arg_pos _ = true

    fun needs_sparens_in_arg_pos Nil = false 
      | needs_sparens_in_arg_pos (App(E,Nil)) = needs_parens_in_arg_pos E
      | needs_sparens_in_arg_pos _ = true

    fun maybe_paren E l = if needs_parens_in_arg_pos E then paren l else l

    fun maybe_sparen S l = if needs_sparens_in_arg_pos S then paren l else l

    fun spine_to_layout sgn S = %%(map (exp_to_layout sgn) (spine_to_list S))
        
    and exp_to_layout sgn (Uni lev) = uni_to_layout lev
      | exp_to_layout sgn (Pi pi) = 
        &[$"PI ",%%[(&[maybe_paren (#arg pi) (exp_to_layout sgn (#arg pi)),$". "]),exp_to_layout sgn (#body pi)]]
      | exp_to_layout sgn (Lam lam) = &[$"LAM. ",exp_to_layout sgn (#body lam)]
      | exp_to_layout sgn (Root(H,Nil)) = head_to_layout sgn H
      | exp_to_layout sgn (Root(H,S)) = &[head_to_layout sgn H,$" ^ ",maybe_sparen S (spine_to_layout sgn S)]

    datatype subelem = SubShift of int | SubExp of exp

    fun sub_to_list (sub as Shift n) = [SubShift n]
      | sub_to_list (Dot(M,sub)) = SubExp M::sub_to_list sub
      | sub_to_list (Comp(s1,s2)) = sub_to_list s1 @ sub_to_list s2

    fun sub_to_layout sgn sub = 
        let
          val sub' = sub_to_list sub 
          fun mapfn (SubShift n) = $("^" ^ Int.toString n)
            | mapfn (SubExp exp) = exp_to_layout sgn exp
          val sub'' = map mapfn sub'
        in
          Layout.list sub''
        end        

  in    
    fun exp_to_string sgn exp = Layout.tostring (exp_to_layout sgn exp) 
    fun spine_to_string sgn sp = Layout.tostring (spine_to_layout sgn sp) 
    fun sub_to_string sgn sub = Layout.tostring (sub_to_layout sgn sub) 
    fun print_exp sgn exp = print ("\n" ^ exp_to_string sgn exp ^ "\n")
    fun print_spine sgn sp = print ("\n" ^ spine_to_string sgn sp ^ "\n")
    fun print_sub sgn sub = print ("\n" ^ sub_to_string sgn sub ^ "\n")
  end
