module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStep
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderInvSumPos
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderLamSumPos

@[expose] public section

/-!
# Halder's step stays positive

The root of the positive quotient in [1, Eq. 26] is positive, so the iteration starting
at a positive `β` stays in the cone `ℝ₊` that [1, Thm. 3] iterates on.

## Inputs
* `β` – weight of the shape sum

## Hypotheses
* `hlam` – every `λᵢ` positive
* `hβ` – `0 ≤ β`

## Conclusion
* the step at `β` is positive

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {ι : Type*} [Fintype ι]
variable {lam : ι → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `g` maps `[0, ∞)` into `(0, ∞)`, as [1, Eq. 26] has it on the cone `ℝ₊`. -/
theorem Ellipsoid.halderStep_pos [Nonempty ι] (hlam : ∀ i, 0 < lam i) {β : ℝ} (hβ : 0 ≤ β) :
    0 < Ellipsoid.halderStep lam β :=
  Real.sqrt_pos.2
    (div_pos (Ellipsoid.halderInvSum_pos hlam hβ) (Ellipsoid.halderLamSum_pos hlam hβ))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
