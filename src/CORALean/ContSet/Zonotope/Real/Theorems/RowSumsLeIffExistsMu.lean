module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# The linear encoding of `‖T‖∞ ≤ α`

[1, Sec. II-B]: `‖T‖∞ ≤ α` (every row has absolute sum at most `α`) holds exactly when each row `tᵢ`
is `Σⱼ (μ⁺ᵢ(j) - μ⁻ᵢ(j)) eⱼ` with `μ⁺ᵢ, μ⁻ᵢ ≥ 0` and `Σⱼ (μ⁺ᵢ(j) + μ⁻ᵢ(j)) = α`. The "only if" needs
a coordinate to put the slack `α - ‖tᵢ‖₁` on, so `ν̂ ≥ 1`: for `ν̂ = 0` and `α > 0` the encoding is
unsatisfiable (`0 = α`) while `‖T‖∞ = 0 ≤ α`.

## Inputs
* `m` – row count
* `r` – column count
* `T` – matrix
* `α` – row-sum bound

## Hypotheses
* `hr` – column count positive

## Conclusion
* row sums are bounded iff each row splits into positive and negative parts

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the Order Reduction
      of Zonotopes". IEEE Control Systems Letters, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. II-B]: `‖T‖∞ ≤ α` iff each row is a point of the `L1`-ball encoded by `μ±`. -/
theorem Zonotope.rowSums_le_iff_exists_mu {m r : ℕ} (T : Mat ℝ m r) (α : ℝ)
    (hr : 0 < r) : -- --- CONCL ---
    (∀ i, ∑ j, |T i j| ≤ α) ↔ ∀ i, ∃ μp μm : Fin r → ℝ, (∀ j, 0 ≤ μp j) ∧ (∀ j, 0 ≤ μm j) ∧
      (∀ j, T i j = μp j - μm j) ∧ ∑ j, (μp j + μm j) = α := by -- --- PROOF ---
  constructor
  · -- split each entry into its positive and negative part, slack on coordinate `0`
    intro h i
    let j0 : Fin r := ⟨0, hr⟩
    let s := (α - ∑ j, |T i j|) / 2
    refine ⟨fun j => max (T i j) 0 + if j = j0 then s else 0,
      fun j => max (-T i j) 0 + if j = j0 then s else 0, fun j => ?_, fun j => ?_, fun j => ?_, ?_⟩
    · have : 0 ≤ s := by have := h i; simp only [s]; linarith
      show 0 ≤ max (T i j) 0 + if j = j0 then s else 0
      split_ifs <;> linarith [le_max_right (T i j) 0]
    · have : 0 ≤ s := by have := h i; simp only [s]; linarith
      show 0 ≤ max (-T i j) 0 + if j = j0 then s else 0
      split_ifs <;> linarith [le_max_right (-T i j) 0]
    · -- `t = t⁺ - t⁻`
      rcases le_total (T i j) 0 with hj | hj <;> simp [hj]
    · -- the parts sum to `‖t‖₁`, the slack to the rest
      have hp : ∀ j, max (T i j) 0 + max (-T i j) 0 = |T i j| := fun j => by
        rcases le_total (T i j) 0 with hj | hj <;> simp [abs_of_nonpos, abs_of_nonneg, hj]
      calc ∑ j, ((max (T i j) 0 + if j = j0 then s else 0)
            + (max (-T i j) 0 + if j = j0 then s else 0))
          = ∑ j, (|T i j| + if j = j0 then 2 * s else 0) := Finset.sum_congr rfl fun j _ => by
            rw [← hp j]; split_ifs <;> ring
        _ = α := by
            simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, s]
            ring
  · -- `|μ⁺ - μ⁻| ≤ μ⁺ + μ⁻`
    intro h i
    obtain ⟨μp, μm, hp, hm, ht, hs⟩ := h i
    calc ∑ j, |T i j| ≤ ∑ j, (μp j + μm j) := Finset.sum_le_sum fun j _ => by
          rw [ht j, abs_le]; constructor <;> linarith [hp j, hm j]
      _ = α := hs

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
