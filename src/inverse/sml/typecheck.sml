
(** eager composition of substitutions, and eager application. *)

structure TypecheckEE =
struct 

  structure L = Lib
  structure Sig = Signat
  structure C = Context
  structure D = Debug

  (* -------------------------------------------------------------------------- *)
  (*  Types                                                                     *)
  (* -------------------------------------------------------------------------- *)

  type const = int 

  datatype uni = Type 
               | Kind
                   
  datatype head = Const of const
                | BVar of int

  datatype depend = No | Maybe

  datatype exp = Uni of uni
               | Pi of pi
               | Lam of lam 
               | Root of head * spine

       and spine = Nil
                 | App of exp * spine

  withtype pi = {var : string option,
                 arg : exp,
                 depend : depend,
                 body : exp}

       and lam = {var : string option,
                  body : exp}

  datatype sub = Dot of exp * sub
               | Shift of int

  type decl = {id : const,
               name : string,
               exp : exp,
               uni : uni}

  type def  = {id : const,
               name : string,
               exp : exp,
               def : exp,
               height : int,
               root : const,
               uni : uni}

  type abbrev = {id : const,
                 name : string,
                 exp : exp,
                 def : exp,
                 uni : uni}

  datatype dec = Decl of decl
               | Def of def
               | Abbrev of abbrev

  type sgn = dec Sig.sgn

  datatype ret = RetExp of exp | RetVar of int

  (* -------------------------------------------------------------------------- *)
  (*  Exceptions                                                                *)
  (* -------------------------------------------------------------------------- *)

  exception Check of string
  exception Fail_exp of string * exp
  exception Fail_exp2 of string * exp * exp
  exception Fail_exp_spine of string * exp * spine
  exception Fail_spine_exp of string * spine * exp
  exception Fail_hd_spine of string * head * spine
  exception Fail_sub_exp of string * sub * exp
  exception Fail_sub_exp of string * sub * exp

  (* -------------------------------------------------------------------------- *)
  (*  Util                                                                      *)
  (* -------------------------------------------------------------------------- *)

  val expType = Uni Type
  val expKind = Uni Kind

  fun bvar n = Root(BVar n,Nil)
  val one = bvar 1
  val shift = Shift 1
  val id_sub = Shift 0

  fun id (Decl decl) = #id decl
    | id (Def def) = #id def
    | id (Abbrev abb) = #id abb

  fun name (Decl decl) = #name decl
    | name (Def def) = #name def
    | name (Abbrev abb) = #name abb

  fun exp (Decl decl) = #exp decl
    | exp (Def def) = #exp def
    | exp (Abbrev abb) = #exp abb

  fun is_def sgn c = 
      case Sig.lookup sgn c of
        Def _ => true
      | Abbrev _ => true
      | Decl _ => false        

  fun def sgn c = 
      case Sig.lookup sgn c of
        Def def => #def def
      | Abbrev abb => #def abb
      | Decl _ => raise Fail "def: not a def"

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

  (* -------------------------------------------------------------------------- *)
  (*  Type Checking                                                             *)
  (* -------------------------------------------------------------------------- *)

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

  and compose (Dot(M,sigma),sigma') = Dot(apply_exp sigma' M,compose(sigma,sigma'))
    | compose (Shift n,Shift m) = Shift (n + m)
    | compose (Shift 0,sigma) = sigma
    | compose (Shift n,Dot(M,sigma)) = compose (Shift (n-1),sigma)

  and push_sub s = Dot(one,compose(s,shift))

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
  (*  Eta                                                                       *)
  (* -------------------------------------------------------------------------- *)

  datatype skel = Base
                | Arrow of skel * skel

  fun card Nil = 0
    | card (App(M,S)) = 1 + card S

  fun num_pi_quants (Pi {body,...}) = 1 + num_pi_quants body
    | num_pi_quants _ = 0

  fun skel_length Base = 0
    | skel_length (Arrow(_,tau)) = 1 + skel_length tau

  fun concat Nil M = App(M,Nil)
    | concat (App(M,S)) M' = App(M,concat S M')

  fun skeleton sgn ctx (Uni Type) = Base
    | skeleton sgn ctx (Root(Const a,S)) = 
      let
        val aty = exp(Sig.lookup sgn a)
        val n = num_pi_quants aty
        val n' = card S
      in
        if n = n' then Base 
        else raise Fail "skeleton: not eta expanded"
      end
    | skeleton sgn ctx (Root(BVar i,S)) = 
      let
        val aty = L.ith (i-1) ctx
        val n = skel_length aty
        val n' = card S
      in
        if n = n' then Base 
        else raise Fail "skeleton: not eta expanded"
      end
    | skeleton sgn ctx (Pi {arg,body,...}) = 
      let
        val tau1 = skeleton sgn ctx arg
        val tau2 = skeleton sgn ctx body
      in
        Arrow(tau1,tau2)
      end
    | skeleton _ _ exp = raise Fail_exp("skeleton: bad case",exp)

  exception Fail_exp_skel of string * exp * skel 

  local
    val changed = ref false
  in

    fun long_exp sgn ctx (exp as Uni Type) Base = exp
      | long_exp sgn ctx (Pi {arg,body,depend,var}) Base =
        let
          val arg' = long_exp sgn ctx arg Base 
          val tau = skeleton sgn ctx arg'
          val body' = long_exp sgn (tau::ctx) body Base 
        in
          Pi {arg=arg',body=body',depend=depend,var=var}
        end
      | long_exp sgn ctx (Lam {var,body}) (Arrow(tau1,tau2)) =
        let
          val body' = long_exp sgn (tau1::ctx) body tau2
        in
          Lam {var=var,body=body'}
        end
      | long_exp sgn ctx (expr as Root(con as Const a,S)) Base =
        let
          val tau = skeleton sgn ctx (exp(Sig.lookup sgn a))
        in
          Root(con,long_spine sgn ctx S tau)
        end
      | long_exp sgn ctx (exp as Root(var as BVar i,S)) Base =
        let
          val tau = L.ith (i-1) ctx (* indices start at 1 *)
        in
          Root(var,long_spine sgn ctx S tau)
        end
      | long_exp sgn ctx (Root(con as Const c,S)) (tau as Arrow(tau1,tau2)) =
        let
          val S' = concat (apply_spine shift S) one
        in
          changed := true;
          long_exp sgn ctx (Lam {var=NONE,body=Root(con,S')}) tau 
        end
      | long_exp sgn ctx (Root(BVar i,S)) (tau as Arrow(tau1,tau2)) =
        let
          val S' = concat (apply_spine shift S) one
        in
          changed := true;
          long_exp sgn ctx (Lam {var=NONE,body=Root(BVar(i+1),S')}) tau 
        end
      | long_exp _ _ exp skel = raise Fail_exp_skel("long_exp: bad case",exp,skel)

    and long_spine sgn ctx Nil Base = Nil
      | long_spine sgn ctx (App(M,S)) (Arrow(tau1,tau2)) =
        let
          val M' = long_exp sgn ctx M tau1 
          val S' = long_spine sgn ctx S tau2
        in
          App(M',S')
        end
      | long_spine _ _ _ _ = raise Fail "long_spine: bad case"

    fun eta_expand sgn exp skel = 
        let
          val () = changed := false
          val exp' = long_exp sgn [] exp skel
        in
          if !changed then L.warning "expression is not eta long" else ();
          exp'
        end

  end

  (* -------------------------------------------------------------------------- *)
  (*  Signatures                                                                *)
  (* -------------------------------------------------------------------------- *)

  structure Sgn =
  struct

    type sgn = dec Sig.sgn

    val empty = Sig.empty

    fun insert sgn (Decl {id,name,exp,uni}) = 
        let
          val exp' = eta_expand sgn exp Base
        in
          check sgn exp' (Uni uni);
          Sig.insert sgn (id,Decl {id=id,name=name,exp=exp',uni=uni})
        end
      | insert sgn (Def {id,name,exp,def,height,root,uni}) =
        let
          val exp' = eta_expand sgn exp Base
          val def' = eta_expand sgn def (skeleton sgn [] exp')
        in
          check sgn exp' (Uni uni);
          check sgn def' exp';
          Sig.insert sgn (id,Def {id=id,name=name,exp=exp',def=def',
                                  height=height,root=root,uni=uni})
        end
      | insert sgn (Abbrev {id,name,exp,def,uni}) =
        let
          val exp' = eta_expand sgn exp Base
          val def' = eta_expand sgn def (skeleton sgn [] exp')
        in
          check sgn exp' (Uni uni);
          check sgn def' exp';
          Sig.insert sgn (id,Abbrev{id=id,name=name,exp=exp',
                                    def=def',uni=uni})
        end

    fun lookup sgn c = Sig.lookup sgn c 

  end

end

