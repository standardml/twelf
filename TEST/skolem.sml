Twelf.reset ();
Twelf.loadFile "TEST/cp.elf";
val SOME cpt = Names.nameLookup "cpt";
val _ = Skolem.install [cpt];
val SOME cpt1 = Names.nameLookup "cpt#1";
val SOME cpt2 = Names.nameLookup "cpt#2";
val _ = TextIO.print (Print.expToString (IntSyn.Null, IntSyn.constType cpt1) ^ "\n");
val _ = TextIO.print (Print.expToString (IntSyn.Null, IntSyn.constType cpt2) ^ "\n");