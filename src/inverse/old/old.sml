(*   and expand_defs sgn (lev as ExpLev _) = lev *)
(*     | expand_defs sgn (ExpPi(U,V)) = ExpPi(expand_defs sgn U,expand_defs sgn V) *)
(*     | expand_defs sgn (ExpLam U) = ExpLam(expand_defs sgn U) *)
(*     | expand_defs sgn (ExpApp(var as HdVar _,S)) = *)
(*       ExpApp(var,expand_defs_spine sgn S) *)
(*     | expand_defs sgn (ExpApp(con as HdConst c,S)) = *)
(*       if not (is_def sgn c) then ExpApp(con,expand_defs_spine sgn S) else *)
(*       let *)
(*         val (Dec decl) = Sig.lookup sgn c *)
(*         val {exp=M,...} = L.the (#def decl) *)
(*       in *)
(*         expand_defs sgn (reduce M S) *)
(*       end *)

(*   and expand_defs_spine sgn SpNil = SpNil *)
(*     | expand_defs_spine sgn (SpCons(M,S)) = SpCons(expand_defs sgn M,expand_defs_spine sgn S) *)
        
(*   and equiv_exp sgn E1 E2 = (expand_defs sgn E1) = (expand_defs sgn E2) *)

(* 
  fun encode_dec (S.Dec decl) = 
      case #def decl of
        NONE => I.ConDec(#name decl,NONE,0,I.Normal,
                         encode_exp (#exp decl),
                         encode_level (#level decl))
      | SOME M => 
        I.ConDef(#name decl,NONE,0,
                 encode_exp (#exp decl),
                 encode_exp M, 
                 encode_level (#level decl),
                 I.Anc(NONE,0,NONE))

  and encode_exp (S.ExpLev l) = I.Uni (encode_level l)
    | encode_exp (S.ExpPi(U,V)) = I.Pi ((I.Dec(NONE,encode_exp U),I.Maybe),encode_exp V)
    | encode_exp (S.ExpLam M) = I.Lam (I.Dec(NONE,I.NVar 0),encode_exp M)
    | encode_exp (S.ExpApp(H,S)) = I.Root (encode_head H,encode_spine S)

  and encode_head (S.Const c) = I.Const c
    | encode_head (S.Var i) = I.BVar i

  and encode_spine S.SpNil = I.Nil
    | encode_spine (S.SpCons(M,S)) = I.App(encode_exp M,encode_spine S)

  and encode_level S.Type = I.Type
    | encode_level S.Kind = I.Kind

  fun dec_to_string (c,dec) = C.conDecToString (encode_dec dec)

  fun exp_to_string (exp,lev) = 
      C.conDecToString (I.ConDec("tmp",NONE,0,I.Normal,encode_exp exp,encode_level lev))
*) 
