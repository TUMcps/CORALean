import CORALean.ContSet.ContSet.Definitions.HyperplanePolyhedron
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The sum of two `S`-band intersections need not be the band of the summed bounds

[1, Sec. 4.2] prints `[m₁, M₁]_S ⊕ [m₂, M₂]_S = [m₁ + m₂, M₁ + M₂]_S`. It fails in the plane
for `S = {e₁, e₂, e₁ + e₂}`, no two directions parallel: `P₁`, with `x, y ∈ [0, 1]` and
`x + y ∈ [0, 9]`, is the unit square, and `P₂`, with `x, y ∈ [0, 9]` and `x + y ∈ [0, 1]`,
the unit triangle. Both are nonempty, but `M₁ = (1, 1, 9)` and `M₂ = (9, 9, 1)` each
have a bound the set does not attain. The summed bounds are `10` in every direction and
admit `(10, 0)`, while every point of `P₁ ⊕ P₂` has `x ≤ 2`. The inclusion that holds is
`ContSet.hyperplanePolyhedron_add_subset`.

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of
      Linear Time-Invariant Systems with Inputs". In Hybrid Systems: Computation and
      Control (HSCC), LNCS 3927, Springer, 2006, pp. 257-271.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean

open Matrix Pointwise


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The dot product in the plane, written out. -/
theorem ContSet.aux_dot_two (x y : Vec ℝ 2) :
    x ⬝ᵥ y = x 0 * y 0 + x 1 * y 1 := by
  simp [dotProduct, Fin.sum_univ_two]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2] is false: two nonempty bands whose sum is not the band of the sums. -/
theorem ContSet.exists_hyperplanePolyhedron_add_ne :
    ∃ (S : Finset (Vec ℝ 2)) (m₁ M₁ m₂ M₂ : Vec ℝ 2 → ℝ),
      (ContSet.hyperplanePolyhedron S m₁ M₁).Nonempty ∧
        (ContSet.hyperplanePolyhedron S m₂ M₂).Nonempty ∧
        ContSet.hyperplanePolyhedron S m₁ M₁ + ContSet.hyperplanePolyhedron S m₂ M₂
          ≠ ContSet.hyperplanePolyhedron S (m₁ + m₂) (M₁ + M₂) := by -- --- PROOF ---
  classical
  -- `S = {e₁, e₂, e₁ + e₂}`; `M₁ = 1 + 8xy` and `M₂ = 9 - 8xy` read `(1, 1, 9)`, `(9, 9, 1)`
  refine ⟨{![1, 0], ![0, 1], ![1, 1]}, 0, fun s => 1 + 8 * (s 0 * s 1), 0,
    fun s => 9 - 8 * (s 0 * s 1), ⟨0, ?_⟩, ⟨0, ?_⟩, fun h => ?_⟩
  · -- the origin is in the square
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;> norm_num
  · -- and in the triangle
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;> norm_num
  · -- `(10, 0)` is in the band of the sums
    have hmem : (![10, 0] : Vec ℝ 2) ∈ ContSet.hyperplanePolyhedron
        ({![1, 0], ![0, 1], ![1, 1]} : Finset (Vec ℝ 2)) (0 + 0)
        ((fun s : Vec ℝ 2 => 1 + 8 * (s 0 * s 1)) + fun s => 9 - 8 * (s 0 * s 1)) := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl <;> rw [ContSet.aux_dot_two] <;> norm_num
    rw [← h] at hmem
    -- but a point of the sum has `x ≤ 1 + 1`
    obtain ⟨p, hp, q, hq, hpq⟩ := hmem
    have hp₁ := (hp ![1, 0] (by simp)).2
    have hq₂ := (hq ![0, 1] (by simp)).1
    have hq₃ := (hq ![1, 1] (by simp)).2
    have hx := congrFun hpq 0
    rw [ContSet.aux_dot_two] at hp₁ hq₂ hq₃
    simp at hp₁ hq₂ hq₃ hx
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
