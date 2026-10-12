import CORALean.ContSet.Taylm.Float.Theorems.ReexpBoxBoundsMem
import CORALean.ContSet.Taylm.Float.Theorems.OptBnbAdvMem
import CORALean.ContSet.Taylm.Float.Theorems.PowBoundsMem
import CORALean.ContSet.Taylm.Float.Theorems.ProdBoundsMem
import CORALean.ContSet.Taylm.Float.Theorems.PolyBoxBoundsMem
import CORALean.ContSet.Taylm.Float.Theorems.HalveBoxCover
import CORALean.ContSet.Taylm.Float.Theorems.SplitAtCovers
import CORALean.ContSet.Taylm.Float.Theorems.ListMinLe
import CORALean.ContSet.Taylm.Float.Theorems.LeListMax
import CORALean.ContSet.Taylm.Float.Theorems.BnbLoopMem
import CORALean.ContSet.Taylm.Float.Theorems.BranchAndBoundMem
import CORALean.ContSet.Taylm.Float.Theorems.OptBnbMem
import CORALean.ContSet.Taylm.Float.Theorems.RepresentsaEmptySetSound
import CORALean.ContSet.Taylm.Float.Theorems.RepresentsaPointSound
import CORALean.ContSet.Taylm.Float.Theorems.GetSymsMem
import CORALean.ContSet.Taylm.Float.Theorems.MmulOuter
import CORALean.ContSet.Taylm.Float.Theorems.MpowerOuter
import CORALean.ContSet.Taylm.Float.Theorems.RdivideOuter
import CORALean.ContSet.Taylm.Float.Theorems.InvOuter
import CORALean.ContSet.Taylm.Float.Theorems.InvBoundGe
import CORALean.ContSet.Taylm.Float.Theorems.InvCoefMem
import CORALean.ContSet.Taylm.Float.Theorems.AbsPolyOfRoundLe
import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem
import CORALean.ContSet.Taylm.Float.Theorems.CodeEvalEncloses
import CORALean.ContSet.Taylm.Float.Theorems.ComposeOuter
import CORALean.ContSet.Taylm.Float.Theorems.ConstOuter
import CORALean.ContSet.Taylm.Float.Theorems.AbsSubLeMaximumSubUp
import CORALean.ContSet.Taylm.Float.Theorems.ExpOuter
import CORALean.ContSet.Taylm.Float.Theorems.IntrinsicEncloses
import CORALean.ContSet.Taylm.Float.Theorems.LogCoefMem
import CORALean.ContSet.Taylm.Float.Theorems.LogOuter
import CORALean.ContSet.Taylm.Float.Theorems.RangeBoundMem
import CORALean.ContSet.Taylm.Float.Theorems.ToRealLeOfBelowPow
import CORALean.ContSet.Taylm.Float.Theorems.TrigCoefMem
import CORALean.ContSet.Taylm.Float.Theorems.UnitRemainderLe
import CORALean.ContSet.Taylm.Float.Theorems.SinOuter
import CORALean.ContSet.Taylm.Float.Theorems.CosOuter
import CORALean.ContSet.Taylm.Float.Theorems.HyperbolicOuter
import CORALean.ContSet.Taylm.Float.Theorems.SinhOuter
import CORALean.ContSet.Taylm.Float.Theorems.CoshOuter
import CORALean.ContSet.Taylm.Float.Theorems.MinusOuter
import CORALean.ContSet.Taylm.Float.Theorems.MtimesOuter
import CORALean.ContSet.Taylm.Float.Theorems.PlusOuter
import CORALean.ContSet.Taylm.Float.Theorems.PolyBoundsMem
import CORALean.ContSet.Taylm.Float.Theorems.PowOuter
import CORALean.ContSet.Taylm.Float.Theorems.SmulOuter
import CORALean.ContSet.Taylm.Float.Theorems.SumOuter
import CORALean.ContSet.Taylm.Float.Theorems.TimesOuter
import CORALean.ContSet.Taylm.Float.Theorems.ToRealTermBounds
import CORALean.ContSet.Taylm.Float.Theorems.UminusOuter
import CORALean.ContSet.Taylm.Float.Theorems.UplusOuter
import CORALean.ContSet.Taylm.Float.Theorems.EmptyExact
import CORALean.ContSet.Taylm.Float.Theorems.BoundDotLe
import CORALean.ContSet.Taylm.Float.Theorems.TanOuter
import CORALean.ContSet.Taylm.Float.Theorems.TanhOuter
import CORALean.ContSet.Taylm.Float.Theorems.TraceOuter
import CORALean.ContSet.Taylm.Float.Theorems.ProdOuter
import CORALean.ContSet.Taylm.Float.Theorems.DetOuter
import CORALean.ContSet.Taylm.Float.Theorems.TaylorOuter
import CORALean.ContSet.Taylm.Float.Theorems.AbsLeMagUp
import CORALean.ContSet.Taylm.Float.Theorems.AtanOuter
import CORALean.ContSet.Taylm.Float.Theorems.ArcsinCoefMem
import CORALean.ContSet.Taylm.Float.Theorems.ArcsinBoundGe
import CORALean.ContSet.Taylm.Float.Theorems.AsinOuter
import CORALean.ContSet.Taylm.Float.Theorems.AcosOuter
import CORALean.ContSet.Taylm.Float.Theorems.SqrtCoefMem
import CORALean.ContSet.Taylm.Float.Theorems.SqrtBoundGe
import CORALean.ContSet.Taylm.Float.Theorems.SqrtOuter
import CORALean.ContSet.Taylm.Float.Theorems.BinomCoefMem
import CORALean.ContSet.Taylm.Float.Theorems.BernsteinStepMem
import CORALean.ContSet.Taylm.Float.Theorems.BernsteinEntryBoundsMem
import CORALean.ContSet.Taylm.Float.Theorems.BoundsProdMem
import CORALean.ContSet.Taylm.Float.Theorems.BernsteinCoeffBoundsMem
import CORALean.ContSet.Taylm.Float.Theorems.MemBernsteinIdx
import CORALean.ContSet.Taylm.Float.Theorems.OptBernsteinMem
import CORALean.ContSet.Taylm.Float.Theorems.PolyOfReexpPairs
import CORALean.ContSet.Taylm.Float.Theorems.ReexpandAtOuter
import CORALean.ContSet.Taylm.Float.Theorems.ReexpandOuter

/-!
# Float Taylor model guarantees, collected

Each float operation encloses what its exact counterpart does; `abs_polyOf_round_le` is the
one rounding argument they all pay through. `codeEval_encloses` carries the enclosure through a
code list, `rangeBound_mem` through range bounding.
-/
