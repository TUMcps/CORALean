import CORALean.ContDynamics.Conform.Theorems.ConformantIffDevSet
import CORALean.ContDynamics.Conform.Theorems.ConformantIffHRep
import CORALean.ContDynamics.Conform.Theorems.ConformantIffLp
import CORALean.ContDynamics.Conform.Theorems.ConformantOfRecording
import CORALean.ContDynamics.Conform.Theorems.CostUnderApprox
import CORALean.ContDynamics.Conform.Theorems.DevSetTemplateZono
import CORALean.ContDynamics.Conform.Theorems.DevSetZeroTemplateZono
import CORALean.ContDynamics.Conform.Theorems.DisjointSingletonAddIff
import CORALean.ContDynamics.Conform.Theorems.FalsifyAddCounterexample
import CORALean.ContDynamics.Conform.Theorems.GloCostEq
import CORALean.ContDynamics.Conform.Theorems.GloSetTemplateZono
import CORALean.ContDynamics.Conform.Theorems.GloStateSpace
import CORALean.ContDynamics.Conform.Theorems.ImageTemplateZono
import CORALean.ContDynamics.Conform.Theorems.IntervalNormProps
import CORALean.ContDynamics.Conform.Theorems.IntervalNormSmul
import CORALean.ContDynamics.Conform.Theorems.LpCostEq
import CORALean.ContDynamics.Conform.Theorems.MeasurementConformance
import CORALean.ContDynamics.Conform.Theorems.MemGloSetIffGen
import CORALean.ContDynamics.Conform.Theorems.MemGloSetIffHRep
import CORALean.ContDynamics.Conform.Theorems.MemReachOutIff
import CORALean.ContDynamics.Conform.Theorems.MemTemplateZonoIff
import CORALean.ContDynamics.Conform.Theorems.MemUnderApproxIff
import CORALean.ContDynamics.Conform.Theorems.QpCostEq
import CORALean.ContDynamics.Conform.Theorems.ReachOutNePrinted
import CORALean.ContDynamics.Conform.Theorems.ReachOutSucc
import CORALean.ContDynamics.Conform.Theorems.ReachSetOfGlo
import CORALean.ContDynamics.Conform.Theorems.ReachSetOfSubset
import CORALean.ContDynamics.Conform.Theorems.SingletonAddTemplateZono
import CORALean.ContDynamics.Conform.Theorems.StateAddDev
import CORALean.ContDynamics.Conform.Theorems.SumTemplateZono
import CORALean.ContDynamics.Conform.Theorems.TemplateZonoAdd
import CORALean.ContDynamics.Conform.Theorems.UnderApproxStepNe
import CORALean.ContDynamics.Conform.Theorems.WhiteConformant

/-!
# What reachset conformance and its identification guarantee, collected

The linear model: `mem_reachOut_iff` subtracts the nominal run, `conformant_iff_devSet`
turns conformance into one inclusion per step, and `conformant_iff_hRep` and
`conformant_iff_lp` make that inclusion linear in the identified centres and stretch
factors, so that every feasible point of the identification programs is conformant;
`lpCost_eq` and `qpCost_eq` are their objectives. `conformant_of_recording` gives
conformance at every horizon from one-step residuals.

Any model: `reachSetOf_glo` and `reachSetOf_subset` reach through the general linear
output approximation, `mem_gloSet_iff_hRep` and `mem_gloSet_iff_gen` are the two
constraint forms, `white_conformant` the soundness of the white-box program and
`costU_le` its cheap lower bound. The `*Counterexample`, `*Ne*` files are the printed
statements that do not hold.
-/
