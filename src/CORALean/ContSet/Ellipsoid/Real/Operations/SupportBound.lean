module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ApplyMulVec
public import CORALean.ContSet.Ellipsoid.Real.Theorems.NormPullbackEq
public import CORALean.Global.SupportFunction.SupportFunction

@[expose] public section

/-!
# An ellipsoid answers any direction in closed form

`sup {⟨d, x⟩ | x ∈ E}` is `⟨d, q⟩ + √(dᵀ Q d)`, CORA's `supportFunc_` and [1, Def. 4]'s
`ℓᵀc + √(ℓᵀQℓ)`. Unlike a halfspace description there is no linear program to solve and no dual
solution to check: `√(dᵀ Q d) = ‖Gᵀ d‖₂` (`norm₂_pullback`), and Cauchy–Schwarz is the whole of
the `≤` direction, for *every* direction at once rather than for the ones a caller enumerated.
That is what makes the conversions out of an ellipsoid tight rather than merely sound.

## Inputs
* `E` – ellipsoid
* `c` – linear functional

## Output
* closed-form support bound of `E` along `c`

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- No linear program and no dual solution: the value is closed form and the
maximum is attained, which `Theorems.SupportBoundAttained` states. -/
noncomputable def Ellipsoid.supportBound (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    SupportBound E.construct c where
  val := c E.q + Real.sqrt (dualVec c ⬝ᵥ E.Q *ᵥ dualVec c)
  le := by
    rw [E.construct_eq_sqrt]
    rintro _ ⟨u, hu, rfl⟩
    rw [map_add, ← E.norm₂_pullback]
    refine add_le_add le_rfl ?_
    calc c (E.G *ᵥ u) = E.pullback c ⬝ᵥ u := E.apply_mulVec c u
      _ ≤ ‖E.pullback c‖₂ * ‖u‖₂ := dotProduct_le_norm₂_mul_norm₂ _ _
      _ ≤ ‖E.pullback c‖₂ * 1 := mul_le_mul_of_nonneg_left hu (norm₂_nonneg _)
      _ = ‖E.pullback c‖₂ := mul_one _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
