module

public import CORALean.ContSet.Zonotope.Real.Definitions.FRadius
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-!
# The derivative of the F-radius along one generator entry

[1, Prop. 8]'s computation: along the entry `G(i,j)` of the generator matrix of `Y = ⟨c, G⟩ ⊂ ℝⁿ`,
the F-radius `(1/n) √(Σ G²)` [1, Prop. 5] has the derivative `G(i,j) / (n² ‖Y‖_F)`, for
`‖Y‖_F > 0`: the sum under the root is `S - G(i,j)² + t²` at `t`, so the derivative is `(1/n) ·
G(i,j) / √S` with `√S = n ‖Y‖_F`. The gradient of [1, Prop. 8] is this at every entry.

## Inputs
* `Y` – zonotope
* `j` – generator index
* `i` – coordinate

## Hypotheses
* `hY` – F-radius positive

## Conclusion
* the F-radius is differentiable in that entry with the stated derivative

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The sum of squares along one entry: `S - G(i,j)² + t²`. -/
theorem Zonotope.aux_sumSq_update (Y : Zonotope (Vec ℝ n)) (j : Fin Y.h) (i : Fin n)
    (t : ℝ) : -- --- CONCL ---
    ∑ i', ∑ j', (Function.update Y.G j (Function.update (Y.G j) i t) j' i') ^ 2 =
      ∑ i', ∑ j', Y.G j' i' ^ 2 + (t ^ 2 - Y.G j i ^ 2) := by -- --- PROOF ---
  have h : ∀ i' j', (Function.update Y.G j (Function.update (Y.G j) i t) j' i') ^ 2 =
      Y.G j' i' ^ 2 + if i' = i ∧ j' = j then t ^ 2 - Y.G j i ^ 2 else 0 := by
    intro i' j'
    by_cases hj : j' = j
    · by_cases hi : i' = i
      · subst hj; subst hi; simp
      · simp [hj, hi]
    · simp [hj]
  simp only [h, Finset.sum_add_distrib]
  congr 1
  simp [ite_and, Finset.sum_ite_eq']


-- =======================================  MAIN THEOREM  ======================================= --

/-- `t ↦` the F-radius with the entry `(j, i)` replaced by `t` has the derivative at `G(j,i)` that
the corrected statement names. -/
theorem Zonotope.fRadius_hasDerivAt (Y : Zonotope (Vec ℝ n)) (hY : 0 < Y.fRadius)
    (j : Fin Y.h) (i : Fin n) : -- --- CONCL ---
    HasDerivAt (fun t => Zonotope.fRadius
      { Y with G := Function.update Y.G j (Function.update (Y.G j) i t) })
      (Y.G j i / ((n : ℝ) ^ 2 * Y.fRadius)) (Y.G j i) := by -- --- PROOF ---
  have hn : (n : ℝ) ≠ 0 := by
    rintro h0
    have : n = 0 := by exact_mod_cast h0
    subst this
    simp [Zonotope.fRadius] at hY
  have hS : 0 < ∑ i', ∑ j', Y.G j' i' ^ 2 := by
    by_contra hle
    have : ∑ i', ∑ j', Y.G j' i' ^ 2 = 0 := le_antisymm (not_lt.mp hle)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    simp [Zonotope.fRadius, this] at hY
  have hq : HasDerivAt (fun t : ℝ => ∑ i', ∑ j', Y.G j' i' ^ 2 + (t ^ 2 - Y.G j i ^ 2))
      (2 * Y.G j i) (Y.G j i) := by
    have := ((hasDerivAt_pow 2 (Y.G j i)).sub_const (Y.G j i ^ 2)).const_add
      (∑ i', ∑ j', Y.G j' i' ^ 2)
    simpa using this
  have hs := hq.sqrt (by simp [hS.ne'])
  have hs' := HasDerivAt.const_mul ((n : ℝ)⁻¹) hs
  refine (hs'.congr_deriv ?_).congr_of_eventuallyEq ?_
  · -- the value of the derivative
    have hsq : Real.sqrt (∑ i', ∑ j', Y.G j' i' ^ 2) = n * Y.fRadius := by
      simp [Zonotope.fRadius, hn]
    simp only [sub_self, add_zero, hsq]
    field_simp
  · exact Filter.Eventually.of_forall fun t =>
      congrArg (fun S => (n : ℝ)⁻¹ * Real.sqrt S) (Zonotope.aux_sumSq_update Y j i t)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
