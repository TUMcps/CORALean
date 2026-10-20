module

public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopePolyZonotopeExact
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# A box as a polynomial zonotope

The box's zonotope, then that zonotope's factors: one dependent factor per coordinate and no
independent generators. Nothing is lost, but only the enclosing direction is stated, since
`Interval.zonotope` states only that: a box whose `sup` falls below its `inf` denotes nothing while
the zonotope built from it does not. `polyZonotope_norm_le` is the other direction in the only form
that survives: a bound in the supremum norm, asking for *both* ends to be small rather than the box
to be ordered, which is what a residual block contributes to a Minkowski inflation.
`polyZonotope_mono` is monotone in the two ends, the narrower box having to be ordered.

## Inputs
* `I` – interval
* `ε` – bound on the ends
* `y` – point

## Hypotheses
* `hε` – bound nonnegative
* `hlo` – lower ends within the bound
* `hhi` – upper ends within the bound
* `hy` – point lies in the polynomial zonotope

## Conclusion
* norm of `y` is at most the bound
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With both ends inside `[-ε, ε]` the whole set is, whichever way round the
box is: a coordinate is a convex combination of its two ends. -/
theorem Interval.polyZonotope_norm_le {I : Interval (Vec ℝ n)} {ε : ℝ} (hε : 0 ≤ ε)
    (hlo : ∀ i, |I.inf i| ≤ ε) (hhi : ∀ i, |I.sup i| ≤ ε) {y : Vec ℝ n}
    (hy : y ∈ I.polyZonotope.construct) : ‖y‖ ≤ ε := by -- --- PROOF ---
  have hz : y ∈ I.zonotope.construct := by
    rw [Zonotope.polyZonotope_exact]
    exact hy
  obtain ⟨β, hβ, rfl⟩ := hz
  rw [pi_norm_le_iff_of_nonneg hε]
  intro i
  -- only the diagonal generator `i` reaches coordinate `i`
  have hsum : (∑ j : Fin n, β j •
        (fun i => if i = j then (I.sup i - I.inf i) / 2 else 0 : Vec ℝ n)) i
      = β i * ((I.sup i - I.inf i) / 2) := by
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp only [Pi.smul_apply, smul_eq_mul, if_neg (Ne.symm hj), mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ i) hc
  show ‖((fun i => (I.inf i + I.sup i) / 2 : Vec ℝ n) + ∑ j : Fin n, β j •
    (fun i => if i = j then (I.sup i - I.inf i) / 2 else 0 : Vec ℝ n)) i‖ ≤ ε
  rw [Pi.add_apply, hsum, Real.norm_eq_abs, abs_le]
  obtain ⟨hb1, hb2⟩ := abs_le.mp (hβ i)
  obtain ⟨hi1, hi2⟩ := abs_le.mp (hlo i)
  obtain ⟨hs1, hs2⟩ := abs_le.mp (hhi i)
  -- the two ends carry weights `(1 ± β) / 2`, both nonnegative and summing to one
  constructor
  · nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 + β i by linarith)
      (show (0:ℝ) ≤ I.sup i + ε by linarith),
      mul_nonneg (show (0:ℝ) ≤ 1 - β i by linarith)
        (show (0:ℝ) ≤ I.inf i + ε by linarith)]
  · nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 + β i by linarith)
      (show (0:ℝ) ≤ ε - I.sup i by linarith),
      mul_nonneg (show (0:ℝ) ≤ 1 - β i by linarith)
        (show (0:ℝ) ≤ ε - I.inf i by linarith)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
