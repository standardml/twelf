structure CSManager = CSManager (structure Global = Global
                                 structure IntSyn = IntSyn
                                 structure Unify = UnifyTrail
                                 structure Fixity = Names.Fixity
                                 structure ModeSyn = ModeSyn);

structure CSEqQ = CSEqDomain (structure Domain = Rationals
                              structure IntSyn = IntSyn
                              structure Whnf = Whnf
                              structure Unify = UnifyTrail
                              structure CSManager = CSManager);

structure CSIneqQ = CSIneqDomain (structure OrderedDomain = Rationals
                                  structure IntSyn = IntSyn
                                  structure Trail = Trail
                                  structure Unify = UnifyTrail
                                  structure SparseArray = SparseArray
                                  structure SparseArray2 = SparseArray2
                                  structure CSManager = CSManager
                                  structure CSEqDomain = CSEqQ);

structure CSEqString = CSEqString (structure IntSyn = IntSyn
                                   structure Whnf = Whnf
                                   structure Unify = UnifyTrail
                                   structure CSManager = CSManager);

structure CSEqBool = CSEqBool (structure IntSyn = IntSyn
                               structure Whnf = Whnf
                               structure Unify = UnifyTrail
                               structure CSManager = CSManager);

CSManager.installSolver (CSEqQ.solver);
CSManager.installSolver (CSIneqQ.solver);
CSManager.installSolver (CSEqString.solver);
CSManager.installSolver (CSEqBool.solver);