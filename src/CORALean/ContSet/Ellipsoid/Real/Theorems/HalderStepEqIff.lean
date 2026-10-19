module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderStepLtIff
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderStepLtSelfIff

@[expose] public section

/-!
# The fixed points of Halder's step are the roots of the stationarity equation

`g(β) = β` iff `∑ᵢ (1 − β²λᵢ)/(1 + βλᵢ) = 0` for `β > 0`: the fixed-point iteration
[1, Eq. 26] is a rewriting of the first-order condition [1, Eq. 18], not an approximation of
it.

## Inputs
* `β` – weight of the shape sum

## Hypotheses
* `hlam` – every `λᵢ` positive
* `hβ` – `0 < β`

## Conclusion
* `β` is fixed by the step iff it solves the stationarity equation

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

/-- A positive `β` is fixed by [1, Eq. 26] iff it solves [1, Eq. 18]. -/
theorem Ellipsoid.halderStep_eq_iff [Nonempty ι] (hlam : ∀ i, 0 < lam i) {β : ℝ} (hβ : 0 < β) :
    Ellipsoid.halderStep lam β = β ↔ Ellipsoid.halderStationarity lam β = 0 := by -- --- PROOF ---
  have h1 := Ellipsoid.lt_halderStep_iff hlam hβ.le
  have h2 := Ellipsoid.halderStep_lt_iff hlam hβ
  constructor
  · -- a fixed point is neither above nor below itself
    intro h
    rcases lt_trichotomy (Ellipsoid.halderStationarity lam β) 0 with hh | hh | hh
    · exact absurd h (ne_of_lt (h2.2 hh))
    · exact hh
    · exact absurd h (ne_of_gt (h1.2 hh))
  · intro h
    rcases lt_trichotomy (Ellipsoid.halderStep lam β) β with hh | hh | hh
    · exact absurd (h2.1 hh) (by rw [h]; exact lt_irrefl _)
    · exact hh
    · exact absurd (h1.1 hh) (by rw [h]; exact lt_irrefl _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
