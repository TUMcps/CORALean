module

public import CORALean.ContDynamics.Conform.Theorems.ClassesVecSingleSubsetIff
public import CORALean.ContDynamics.Conform.Theorems.ConformantIffDevSet
public import CORALean.ContDynamics.Conform.Theorems.ConformantIffHRep
public import CORALean.ContDynamics.Conform.Theorems.ConformantIffLp
public import CORALean.ContDynamics.Conform.Theorems.ConformantOfRecording
public import CORALean.ContDynamics.Conform.Theorems.ConvexFitsUnder
public import CORALean.ContDynamics.Conform.Theorems.CostUnderApprox
public import CORALean.ContDynamics.Conform.Theorems.CpScenarioTermLe
public import CORALean.ContDynamics.Conform.Theorems.DevSetTemplateZono
public import CORALean.ContDynamics.Conform.Theorems.DevSetZeroTemplateZono
public import CORALean.ContDynamics.Conform.Theorems.DisjointSingletonAddIff
public import CORALean.ContDynamics.Conform.Theorems.GloCostEq
public import CORALean.ContDynamics.Conform.Theorems.GloSetTemplateZono
public import CORALean.ContDynamics.Conform.Theorems.GloStateSpace
public import CORALean.ContDynamics.Conform.Theorems.ImageTemplateZono
public import CORALean.ContDynamics.Conform.Theorems.IntervalNormProps
public import CORALean.ContDynamics.Conform.Theorems.IntervalNormSmul
public import CORALean.ContDynamics.Conform.Theorems.LpCostEq
public import CORALean.ContDynamics.Conform.Theorems.MeasurementConformance
public import CORALean.ContDynamics.Conform.Theorems.MemGloSetIffGen
public import CORALean.ContDynamics.Conform.Theorems.MemGloSetIffHRep
public import CORALean.ContDynamics.Conform.Theorems.MemReachOutIff
public import CORALean.ContDynamics.Conform.Theorems.MemTemplateZonoIff
public import CORALean.ContDynamics.Conform.Theorems.MemTemplateZonoIffGen
public import CORALean.ContDynamics.Conform.Theorems.MemUnderApproxIff
public import CORALean.ContDynamics.Conform.Theorems.MemZcpSetIff
public import CORALean.ContDynamics.Conform.Theorems.NotIsBoundaryPointIff
public import CORALean.ContDynamics.Conform.Theorems.QpCostEq
public import CORALean.ContDynamics.Conform.Theorems.ReachOutNePrinted
public import CORALean.ContDynamics.Conform.Theorems.ReachOutSucc
public import CORALean.ContDynamics.Conform.Theorems.ReachSetOfGlo
public import CORALean.ContDynamics.Conform.Theorems.ReachSetOfSubset
public import CORALean.ContDynamics.Conform.Theorems.SearchOutliersOptimal
public import CORALean.ContDynamics.Conform.Theorems.SingletonAddTemplateZono
public import CORALean.ContDynamics.Conform.Theorems.StateAddDev
public import CORALean.ContDynamics.Conform.Theorems.SumTemplateZono
public import CORALean.ContDynamics.Conform.Theorems.TemplateZonoAdd
public import CORALean.ContDynamics.Conform.Theorems.UnderApproxStepNe
public import CORALean.ContDynamics.Conform.Theorems.WhiteConformant
public import CORALean.ContDynamics.Conform.Theorems.ZcpBoundaryLp
public import CORALean.ContDynamics.Conform.Theorems.ZcpClassificationLp
public import CORALean.ContDynamics.Conform.Theorems.ZcpClassificationMilp
public import CORALean.ContDynamics.Conform.Theorems.ZcpIntervalNorm
public import CORALean.ContDynamics.Conform.Theorems.ZcpRegressionLp
public import CORALean.ContDynamics.Conform.Theorems.ZcpRegressionMilp
public import CORALean.ContDynamics.Conform.Theorems.ZcpSetEq
public import CORALean.ContDynamics.Conform.Theorems.PassesBFOfConformant
public import CORALean.ContDynamics.Conform.Theorems.GloInputOutput
public import CORALean.ContDynamics.Conform.Theorems.NarxWindowStep
public import CORALean.ContDynamics.Conform.Theorems.ProdJacSucc
public import CORALean.ContDynamics.Conform.Theorems.SumWindow
public import CORALean.ContDynamics.Conform.Theorems.UnrollAffine

/-!
# What reachset conformance and its identification guarantee, collected

The linear model: `mem_reachOut_iff` subtracts the nominal run, `conformant_iff_devSet`
turns conformance into one inclusion per step, and `conformant_iff_hRep` and
`conformant_iff_lp` make that inclusion linear in the identified centers and stretch
factors, so that every feasible point of the identification programs is conformant;
`lpCost_eq` and `qpCost_eq` are their objectives. `conformant_of_recording` gives
conformance at every horizon from one-step residuals.

Any model: `reachSetOf_glo` and `reachSetOf_subset` reach through the general linear
output approximation, `mem_gloSet_iff_hRep` and `mem_gloSet_iff_gen` are the two
constraint forms, `passesBF_of_conformant` the brute-force check's soundness, `white_conformant`
the soundness of the white-box program and `costU_le` its cheap lower bound. The
`*Counterexample`, `*Ne*` files are the printed statements that do not hold.

Zono-conformal prediction: `zcpSet_eq`, `mem_zcpSet_iff` and `intervalNorm_zcpSet` describe the
prediction zonotope, `zcp_regression_lp` and `zcp_classification_lp` make its identification a
linear program, `zcp_regression_milp` and `zcp_classification_milp` add outliers, and
`isBoundaryPoint_iff_lp23` and `searchOutliers_optimal` find them.
-/
