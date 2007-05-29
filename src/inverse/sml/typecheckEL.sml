

structure TypecheckEL =
struct 

  structure L = Lib
  structure S = Syntax
  structure Sig = S.Signat
  structure C = Context
  structure D = Debug

  open S

  fun check_exp sgn ctx (Uni Type) (Uni Kind) = ()
    | check_exp sgn ctx (Lam {body=M,...}) (Pi {var,arg=U,body=V,...}) =
      check_exp sgn (C.push ctx (var,U)) M V
    | check_exp sgn ctx (Root(Const con,S)) V = 
      let 
        (* pull some common code out of the following case *)
        fun foc exp =
           let
             val U = focus sgn ctx S exp
           in
             if equiv_exp sgn U V then ()
             else raise Check "check_exp: exps not equivalent"
           end
      in
        case Sig.lookup sgn con of
           Decl decl => foc (#exp decl) 
         | Def def => foc (#exp def)
         (* why does this fail?*)
         | Abbrev abbrev => raise Fail "check_exp: abbrev"
      end
    | check_exp sgn ctx (Root(BVar i,S)) V = 
      (case C.lookup ctx (i-1) (* DeBruijn indices start at 1 *) of
         SOME (_,A) =>
         let
           val U = focus sgn ctx S (apply_exp (Shift i) A) 
         in
           if equiv_exp sgn U V then ()
           else raise Fail_exp2("check_exp: Root,BVar",U,V)
         end
       | NONE => raise Check ("focus: var out of bounds"))
    | check_exp sgn ctx (Pi {var,arg=A1,body=A2,...}) (uni as Uni _) = 
      (check_exp sgn ctx A1 expType;
       check_exp sgn (C.push ctx (var,A1)) A2 uni)
    | check_exp _ _ _ _ = raise Check "check: bad case"

  and focus sgn ctx Nil (ty as Uni Type) = ty
    | focus sgn ctx Nil (hd as Root (Const _,_)) = hd
    | focus sgn ctx (App(M,S)) (Pi {arg=A1,body=A2,...}) =
      (check_exp sgn ctx M A1;
       focus sgn ctx S (apply_exp (Dot(M,id_sub)) A2))
    | focus _ _ S E = raise Fail_spine_exp("focus: bad case",S,E)

  and check sgn E1 E2 = check_exp sgn C.empty E1 E2
 
  (* -------------------------------------------------------------------------- *)
  (*  Substitutions                                                             *)
  (* -------------------------------------------------------------------------- *)

  and apply_exp _ (uni as Uni _) = uni
    | apply_exp sub (Pi {var,arg=U,depend,body=V}) =
      Pi {var = var,
           arg = apply_exp sub U,
           depend = depend,
           body = apply_exp (push_sub sub) V}
    | apply_exp sub (Lam {var,body=U}) =
      Lam {var=var,
           body=apply_exp (push_sub sub) U}
    | apply_exp sub (exp as Root(H,S)) =
      let
        val S' = apply_spine sub S
      in
        case H of
          Const _ => Root(H,S')
        | BVar i =>
          case apply_var sub i of
            RetVar j => Root(BVar j,S')
          | RetExp M => reduce M S'
      end

  and apply_spine sub Nil = Nil
    | apply_spine sub (App(M,S)) = App(apply_exp sub M,apply_spine sub S)

  and apply_var (Dot(M,sub)) i =
      if i = 1 
      then 
        case M of 
          Root(BVar j,Nil) => RetVar j
        | _ => RetExp M
      else apply_var sub (i-1)
    | apply_var (Shift n) i = RetVar (i+n)
    | apply_var (Comp(s1,s2)) i = 
      case apply_var s1 i of
        RetVar j => apply_var s2 j
      | RetExp M => RetExp(apply_exp s2 M)

  and compose s1 s2 = Comp(s1,s2)

  and push_sub s = Dot(one,compose s shift)

  (* -------------------------------------------------------------------------- *)
  (*  Beta                                                                      *)
  (* -------------------------------------------------------------------------- *)

  and reduce (exp as Root(_,_)) Nil = exp
    | reduce (Lam {body=M,...}) (App(M',S)) =
      reduce (apply_exp (Dot(M',id_sub)) M) S
    | reduce E S = raise Fail_exp_spine ("reduce: bad case: head: ",E,S)

  (* -------------------------------------------------------------------------- *)
  (*  Equivalence wrt Definitions                                               *)
  (* -------------------------------------------------------------------------- *)

  and equiv_exp sgn (Uni u1) (Uni u2) = u1 = u2
    | equiv_exp sgn (Pi {arg=U1,body=V1,...}) (Pi {arg=U2,body=V2,...}) =
      equiv_exp sgn U1 U2 andalso equiv_exp sgn V1 V2
    | equiv_exp sgn (Lam {body=U,...}) (Lam {body=U',...}) =
      equiv_exp sgn U U'
    | equiv_exp sgn (Root(BVar i,S1)) (Root(BVar i',S2)) =
      i = i' andalso equiv_spine sgn S1 S2
    | equiv_exp sgn (exp as Root(Const c,S)) (exp' as Root(Const c',S')) =
      if c = c' then equiv_spine sgn S S' else
      (case (Sig.lookup sgn c,Sig.lookup sgn c') of
         (Decl decl,Def def) =>
         if #root def <> #id decl then false
         else equiv_exp sgn exp (reduce (#def def) S')
       | (Def def,Decl decl) =>
         if #root def <> #id decl then false
         else equiv_exp sgn (reduce (#def def) S) exp'
       | (Abbrev {def,...},_) => equiv_exp sgn (reduce def S) exp'
       | (_,Abbrev {def,...}) => equiv_exp sgn exp (reduce def S')
       | (Def {def=def,height=h,root=rc,...},
          Def {def=def',height=h',root=rc',...}) =>
         if rc <> rc' then false else
         if h = h' then equiv_exp sgn (reduce def S) (reduce def' S')
         else if h > h' then equiv_exp sgn (reduce def S) exp'
         else equiv_exp sgn exp (reduce def' S')
       | (_,_) => raise Check "equiv_exp: bad case")
    | equiv_exp _ _ _ = false

  and equiv_spine sgn Nil Nil = true
    | equiv_spine sgn (App(E,S)) (App(E',S')) =
      equiv_exp sgn E E' andalso equiv_spine sgn S S'
    | equiv_spine _ _ _ = false

  (* -------------------------------------------------------------------------- *)
  (*  Signatures                                                                *)
  (* -------------------------------------------------------------------------- *)

  fun check_dec (c,Decl {id,name,exp,uni}) = 
      let
        val uni' = Uni uni
        val exp' = eta_expand(exp,uni')
      in
        check exp' uni';
        Sig.insert (id,Decl {id=id,name=name,exp=exp',uni=uni})
      end
    | check_dec (c,Def {id,name,exp,def,height,root,uni}) =
      let
        val uni' = Uni uni
        val exp' = eta_expand(exp,uni')
        val def' = eta_expand(def,exp')
      in
        check exp' uni';
        check def' exp';
        Sig.insert (id,Def {id=id,name=name,exp=exp',def=def',
                            height=height,root=root,uni=uni})
      end
    | check_dec (c,Abbrev {id,name,exp,def,uni}) =
      let
        val uni' = Uni uni
(*         val exp' = eta_expand(exp,uni') *)
(*         val def' = eta_expand(def,exp') *)
        val exp' = exp
        val def' = def
      in
        check exp' uni';
        check def' exp';
        Sig.insert (id,Abbrev{id=id,name=name,exp=exp',
                              def=def',uni=uni})
      end

  fun check_signat' decs = 
      List.app (fn (decl as (c,dec)) => 
                   ((* L.printl ("checking: " ^ name dec ); *)
                    check_dec decl)) decs

  fun check_signat decs = (Timers.time Timers.checking check_signat') decs

  fun check_signat_clear decs = 
      (Sig.reset();
       check_signat decs)

end

