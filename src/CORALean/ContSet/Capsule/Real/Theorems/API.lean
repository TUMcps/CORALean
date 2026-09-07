import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqEmpty
import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqAdd
import CORALean.ContSet.Capsule.Real.Theorems.Convex
import CORALean.ContSet.Capsule.Real.Theorems.IsCompact
import CORALean.ContSet.Capsule.Real.Theorems.OfPointMem

/-!
# What a capsule guarantees, collected

`construct_eq_empty` and `construct_eq_add` are the shared case split, at
`C.r < 0` and `0 ≤ C.r`; `convex_construct` and `isCompact_construct` both
transfer their property from the segment and the ball that split produces.
`mem_ofPoint` needs neither: at `g = 0` and `r = 0` the defining bound holds
at any `t`.
-/
