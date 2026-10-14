module

public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachCZFloat
public import CORALean.ContSet.HPolytope.Float.Theorems.MinkDiffOfInner
public import CORALean.ContSet.Conversion.Float.Theorems.Basic

@[expose] public section

/-!
# The float `CZ(P ⊖ Ẑ_W(τ_k))` is inside the eroded polytope

`maxBackReachCZFloat` is `HPolytope.conZonotopeInner` of `P.minkDiffOf Ẑ_W`: the first is inside
`P ⊖ Ẑ_W` by `minkDiffOf_inner`, whose equality-row condition is asked of the subtrahend, and the
second is inside the polytope it converts, wherever its box lies.
The lines are those of [1, Alg. 3].

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic
open scoped Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Line 11 in floats is inside `P ⊖ Ẑ_W`, at every conversion box. -/
theorem LinearSys.maxBackReachCZFloat_inner (Bx : Interval (Vec 𝕋 n)) (P : HPolytope 𝕋 (Vec 𝕋 n))
    (ZW : Zonotope (Vec 𝕋 n)) (hker : ∀ i, ∀ y ∈ ZW.construct, (toRealMat P.Ae *ᵥ y) i = 0) :
    (LinearSys.maxBackReachCZFloat Bx P ZW).construct ⊆
      minkowskiDiff P.construct ZW.construct := fun _ hx =>
  HPolytope.minkDiffOf_inner _ _ _ hker (HPolytope.conZonotopeInner_subset _ Bx hx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
