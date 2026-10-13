module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# The largest cube in a halfspace

`[1, Lemma 3]`: the largest cube `r [-1, 1]ⁿ` inside `H = {bᵀ x ≤ 1}` has `r = 1 / ‖b‖₁`.
The cube is the supremum-norm ball, and over it `bᵀ x` peaks at `r · sign(b)` with value
`r ‖b‖₁`; so the cube fits iff `r ‖b‖₁ ≤ 1`. "Largest" needs `b ≠ 0`, which the printed
statement leaves out: at `b = 0` every cube fits.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem cube_subset_halfspace_iff (b : Vec ℝ n) :
    (∀ r : ℝ, 0 ≤ r →
      ((∀ x : Vec ℝ n, ‖x‖ ≤ r → ∑ i, b i * x i ≤ 1) ↔ r * ∑ i, |b i| ≤ 1)) ∧
      (b ≠ 0 → IsGreatest {r | 0 ≤ r ∧ ∀ x : Vec ℝ n, ‖x‖ ≤ r → ∑ i, b i * x i ≤ 1}
        (1 / ∑ i, |b i|)) := by -- --- PROOF ---
  have key : ∀ r : ℝ, 0 ≤ r →
      ((∀ x : Vec ℝ n, ‖x‖ ≤ r → ∑ i, b i * x i ≤ 1) ↔ r * ∑ i, |b i| ≤ 1) := by
    intro r hr
    constructor
    -- the corner `r · sign(b)` attains `r ‖b‖₁`
    · intro h
      have hx := h (fun i => if 0 ≤ b i then r else -r)
        ((pi_norm_le_iff_of_nonneg hr).mpr fun i => by split_ifs <;> simp [abs_of_nonneg hr])
      refine le_trans (le_of_eq ?_) hx
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hb
      · rw [abs_of_nonneg hb, mul_comm]
      · rw [abs_of_neg (lt_of_not_ge hb)]; ring
    · intro h x hx
      calc ∑ i, b i * x i ≤ ∑ i, |b i| * r := Finset.sum_le_sum fun i _ => by
            calc b i * x i ≤ |b i * x i| := le_abs_self _
              _ = |b i| * |x i| := abs_mul _ _
              _ ≤ |b i| * r := mul_le_mul_of_nonneg_left
                  ((norm_le_pi_norm x i).trans hx) (abs_nonneg _)
        _ = r * ∑ i, |b i| := by rw [← Finset.sum_mul, mul_comm]
        _ ≤ 1 := h
  refine ⟨key, fun hb => ?_⟩
  -- `‖b‖₁ > 0`, and the admissible radii are `[0, 1 / ‖b‖₁]`
  have hpos : 0 < ∑ i, |b i| := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
    exact lt_of_lt_of_le (abs_pos.mpr hi)
      (Finset.single_le_sum (f := fun i => |b i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  refine ⟨⟨by positivity, (key _ (by positivity)).mpr (by field_simp; rfl)⟩, ?_⟩
  rintro r ⟨hr, h⟩
  rw [le_div_iff₀ hpos]
  simpa using (key r hr).mp h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
