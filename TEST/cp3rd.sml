local 
  open FunSyn;
  open FunTypeCheck;
  structure I = IntSyn 

  val _ = Twelf.loadFile "cp.elf"

  val exp = I.Root (I.Const (valOf (Names.nameLookup ("exp"))), I.Nil)
  val exp' =  I.Root (I.Const (valOf (Names.nameLookup ("exp'"))), I.Nil)
  val cp =  I.Const (valOf (Names.nameLookup ("cp")))
  val lam =  I.Const (valOf (Names.nameLookup ("lam")))
  val lam' =  I.Const (valOf (Names.nameLookup ("lam'")))
  val cp_lam =  I.Const (valOf (Names.nameLookup ("cp_lam")))
  val app =  I.Const (valOf (Names.nameLookup ("app")))
  val app' =  I.Const (valOf (Names.nameLookup ("app'")))
  val cp_app =  I.Const (valOf (Names.nameLookup ("cp_app")))
  val callcc =   I.Const (valOf (Names.nameLookup ("callcc")))
  val callcc' =   I.Const (valOf (Names.nameLookup ("callcc'")))
  val cp_callcc =   I.Const (valOf (Names.nameLookup ("cp_callcc")))


     
  val one = I.Root (I.BVar 1, I.Nil)
  val two = I.Root (I.BVar 2, I.Nil)
  val three = I.Root (I.BVar 3, I.Nil)
  val four = I.Root (I.BVar 4, I.Nil)
  val five = I.Root (I.BVar 5, I.Nil)
  val six = I.Root (I.BVar 6, I.Nil)

  (* the copy function theorem, internal format *)
    
  val cpt_theorem = 
    All (Prim (I.Dec (SOME "E", exp)),
    Ex (I.Dec (SOME "E'", exp'),
    Ex (I.Dec (SOME "D", I.Root (cp, I.App (two, I.App (one, I.Nil)))),
    True)))
   
  fun union (G, I.Null) = G
    | union (G, I.Decl (G', D)) = I.Decl (union(G, G'), D)
    
  fun makectx (I.Null) = I.Null
    | makectx (I.Decl (G, Prim D)) = I.Decl (makectx G, D)
    | makectx (I.Decl (G, Block (CtxBlock (l, G')))) = union (makectx G, G')
    
  fun printCtx (I.Null) = ()
    | printCtx (I.Decl (G, Prim (D))) = 
        (printCtx G;
        TextIO.print (Print.decToString (makectx G, D) ^ "\n"))
    | printCtx (I.Decl (G, _)) = 
        (printCtx G; TextIO.print ("BLOCK\n"))
	 
  fun print (Psi, U) = 
    TextIO.print (Print.expToString (makectx Psi, U) ^ "\n")
	

  val cpt_proof = 
  Rec (MDec (SOME "IH", cpt_theorem),
    Lam (Prim (I.Dec (SOME "E", exp)), 
      Case (Opts 
        [(I.Decl(I.Null, 
	  Block (CtxBlock (SOME 1, 
	  I.Decl( I.Decl (I.Decl (I.Null, 
	  I.Dec (SOME "x", exp)), 
	  I.Dec (SOME "y", exp')),
	  I.Dec (SOME "u", I.Root (cp, I.App (two, I.App (one, I.Nil)))))))), 
 
	  I.Dot (I.Idx 3, I.id),

	  Inx (two, Inx (one, Unit)))
(* ------------------------------------------------------------------------ *)
,         (I.Decl (I.Decl (I.Null, 
	  Block (CtxBlock (SOME 2, 
            I.Decl( I.Decl (I.Decl (I.Null, 
            I.Dec (SOME "c", I.Pi ((I.Dec (NONE, exp), I.No), exp))), 
	    I.Dec (SOME "d", I.Pi ((I.Dec (NONE, exp'), I.No), exp'))),
            I.Dec (SOME "e", I.Pi ((I.Dec (SOME "x", exp), I.Maybe),
			      I.Pi ((I.Dec (SOME "y", exp'), I.Maybe),
			       I.Pi ((I.Dec (NONE, I.Root (cp, I.App (two, I.App (one, I.Nil)))), I.No),
				 I.Root (cp, I.App (I.Root (I.BVar (5), I.App (three, I.Nil)),
				             I.App (I.Root (I.BVar (4), I.App (two, I.Nil)), I.Nil))))))))))),
	    Prim (I.Dec (SOME "E", exp))),
 
	  I.Dot (I.Exp (I.Root (I.BVar 4, I.App (one, I.Nil)), exp), I.id),

	  Let (App ((1, one), 
		    Split (1, 
			   Split(1, Empty))),
	       Inx (I.Root (I.BVar 5, I.App (two, I.Nil)), 
	       Inx (I.Root (I.BVar 4, I.App (three, I.App (two, I.App (one, I.Nil)))), Unit))))
(* ------------------------------------------------------------------------ *)
,	 (I.Decl (I.Null, 
	  Prim (I.Dec (SOME "E1", I.Pi ((I.Dec (SOME "x", exp), I.No), exp)))),

	  I.Dot (I.Exp (I.Root (lam, I.App (one, I.Nil)), exp), I.Shift 1),
	 
	  Let (New (CtxBlock (SOME 1,
		    I.Decl( I.Decl (I.Decl (I.Null, 
		    I.Dec (SOME "x", exp)), 
		    I.Dec (SOME "y", exp')),
	            I.Dec (SOME "u", I.Root (cp, I.App (two, I.App (one, I.Nil)))))),
		    App ((1, I.Redex (four, I.App (three, I.Nil))), 
		    Split (1, 
		    Split (1, Empty)))),

	       Inx (I.Root (lam', I.App (two, I.Nil)),
	       Inx (I.Root (cp_lam, I.App (three, I.App (two,
	       I.App (one, I.Nil)))), Unit))))
(* ------------------------------------------------------------------------ *)
,	 (I.Decl (I.Decl (I.Null, 
	  Prim (I.Dec (SOME "E1", exp))), 
	  Prim (I.Dec (SOME "E2", exp))),

	  I.Dot (I.Exp (I.Root (app, I.App (two, I.App (one, I.Nil))), exp), I.Shift 2),
 

	  Let (App ((1, two), 
	       Split (1, 
	       Split (1, 
	       App ((4, three),
	       Split (1, 
	       Split (1, Empty)))))),
	       Inx (I.Root (app', I.App (four, I.App (two, I.Nil))),
	       Inx (I.Root (cp_app, I.App (five, I.App (two, I.App (six, 
	       I.App (four, I.App (one, I.App (three, I.Nil))))))), Unit))))
(* ------------------------------------------------------------------------- *)
,        (I.Decl (I.Null,
	  Prim (I.Dec (SOME "E1", I.Pi ((I.Dec (SOME "x", 
              I.Pi ((I.Dec (NONE, exp), I.No), exp)), I.No), exp)))),

	  I.Dot (I.Exp (I.Root (callcc, I.App (one, I.Nil)), exp), I.Shift 1),
	 
	  Let (New (CtxBlock (SOME 2,
            I.Decl( I.Decl (I.Decl (I.Null, 
            I.Dec (SOME "c", I.Pi ((I.Dec (NONE, exp), I.No), exp))), 
	    I.Dec (SOME "d", I.Pi ((I.Dec (NONE, exp'), I.No), exp'))),
            I.Dec (SOME "e", I.Pi ((I.Dec (SOME "x", exp), I.Maybe),
			      I.Pi ((I.Dec (SOME "y", exp'), I.Maybe),
			       I.Pi ((I.Dec (NONE, I.Root (cp, I.App (two, I.App (one, I.Nil)))), I.No),
				 I.Root (cp, I.App (I.Root (I.BVar (5), I.App (three, I.Nil)),
				             I.App (I.Root (I.BVar (4), I.App (two, I.Nil)), I.Nil))))))))),

		    App ((1, I.Redex (four, I.App (three, I.Nil))), 
		    Split (1, 
		    Split (1, Empty)))),

	       Inx (I.Root (callcc', I.App (two, I.Nil)),
	       Inx (I.Root (cp_callcc, I.App (three, I.App (two,
	       I.App (one, I.Nil)))), Unit))))


(* ------------------------------------------------------------------------- *)
       ])))


in 
  val print = print
  val printCtx = printCtx
  val cpt_proof = cpt_proof
  val cpt_theorem = cpt_theorem
  val _ = check (cpt_proof, cpt_theorem) 
    handle Error s => TextIO.print (s ^ "\n")
	 | TypeCheck.Error s => TextIO.print (s ^ "\n")
end