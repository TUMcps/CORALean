module

public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachCZ
public import CORALean.ContDynamics.LinearSys.Theorems.MaxBackReachCZFloatInner
public import CORALean.ContDynamics.LinearSys.Theorems.MinkowskiDiffSubsetMaxBackReachCZ

@[expose] public section

/-!
# The float `CZ(P ⊖ Ẑ_W(τ_k))` is inside the exact layer's

`maxBackReachCZFloat_inner` puts the float set in `P ⊖ Ẑ_W`, and that difference is inside the
exact layer's `maxBackReachCZ` (`minkowskiDiff_subset_maxBackReachCZ`). The erosion is monotone
in the right directions: a float polytope inside the exact one, and an exact subtrahend inside
the float one, leave the float difference inside the exact.
The lines are those of [1, Alg. 3].

## Inputs
* `Bx` – conversion box
* `P` – float polytope
* `ZW` – float disturbance zonotope
* `Pr` – exact polytope
* `ZWr` – exact disturbance zonotope

## Hypotheses
* `ρ` – support oracle for exact polytopes
* `hP` – float polytope inside the exact one
* `hZ` – exact zonotope inside the float one
* `hker` – equality rows of the float polytope vanish on the zonotope
* `hkerr` – exact polytope has no equality rows

## Conclusion
* the float conversion lies inside the exact layer's conversion

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

/-- Line 11 in floats is inside the exact layer's `CZ(P ⊖ Ẑ_W(τ_k))`, for a float polytope inside
the exact one and an exact disturbance set inside the float one. -/
theorem LinearSys.maxBackReachCZFloat_subset
    (ρ : ∀ (P : Real.HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (Bx : Interval (Vec 𝕋 n)) (P : HPolytope 𝕋 (Vec 𝕋 n)) (ZW : Zonotope (Vec 𝕋 n))
    (Pr : Real.HPolytope (Vec ℝ n)) (ZWr : Real.Zonotope (Vec ℝ n))
    (hP : P.construct ⊆ Pr.construct) (hZ : ZWr.construct ⊆ ZW.construct)
    (hker : ∀ i, ∀ y ∈ ZW.construct, (toRealMat P.Ae *ᵥ y) i = 0)
    (hkerr : ∀ (i : Fin Pr.me) (y : Vec ℝ n), Pr.Ae i y = 0) : -- --- CONCL ---
    (LinearSys.maxBackReachCZFloat Bx P ZW).construct ⊆
      (LinearSys.maxBackReachCZ ρ Pr ZWr).construct := fun _ hx =>
  LinearSys.minkowskiDiff_subset_maxBackReachCZ ρ Pr ZWr hkerr
    (fun y hy => hP (LinearSys.maxBackReachCZFloat_inner Bx P ZW hker hx y (hZ hy)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
