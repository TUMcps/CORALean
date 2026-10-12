import CORALean.ContSet.PolyZonotope.Real.Theorems.IsPolytopeCexCoraVertex
import CORALean.ContSet.PolyZonotope.Real.Theorems.IsPolytopeCexCoraNormalCone
import CORALean.ContSet.PolyZonotope.Real.Operations.InCone
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# A corner difference lies in the normal cone

For corners of `isPolytopeCex` with factors `±1`, the difference of two corner images is in the
cone of the first corner's columns once two sign conditions hold.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_isPolytopeCex_sign {x : ℝ} (h : x = 1 ∨ x = -1) :
    ((SignType.sign x : SignType) : ℝ) = x := by
  rcases h with rfl | rfl <;> simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- For corners with factors `±1`, the difference of two corner images is in the cone as soon as
`b` and `a c` of the first corner have the opposite signs of the two coordinates of it. -/
theorem PolyZonotope.isPolytopeCex_inCone (I J : Fin 3 → ℝ) (hI : ∀ i, I i = 1 ∨ I i = -1)
    (hdx : I 1 * (2 * J 0 + J 1 - (2 * I 0 + I 1)) ≤ 0)
    (hdy : I 0 * I 2 * (J 0 * J 2 - I 0 * I 2) ≤ 0) :
    inCone (PolyZonotope.isPolytopeCex.coraNormalCone I)
      (PolyZonotope.isPolytopeCex.coraVertex J -
        PolyZonotope.isPolytopeCex.coraVertex I) := by -- --- PROOF ---
  have h : ∀ i, I i ≠ 0 := fun i => by rcases hI i with h | h <;> simp [h]
  have s0 := aux_isPolytopeCex_sign (hI 0)
  have s1 := aux_isPolytopeCex_sign (hI 1)
  have s2 := aux_isPolytopeCex_sign (hI 2)
  have q1 : I 1 * I 1 = 1 := by rcases hI 1 with h | h <;> simp [h]
  have q2 : I 0 * I 2 * (I 0 * I 2) = 1 := by
    rcases hI 0 with h | h <;> rcases hI 2 with h' | h' <;> simp [h, h']
  -- coefficients: `0` on the first column, `-b dx` on the second, `-(a c) dy` on the third
  refine ⟨![0, -I 1 * (2 * J 0 + J 1 - (2 * I 0 + I 1)), -(I 0 * I 2) * (J 0 * J 2 - I 0 * I 2)],
    ?_, ?_⟩
  · intro j
    fin_cases j
    · show (0 : ℝ) ≤ 0
      exact le_rfl
    · show 0 ≤ -I 1 * (2 * J 0 + J 1 - (2 * I 0 + I 1))
      linarith
    · show 0 ≤ -(I 0 * I 2) * (J 0 * J 2 - I 0 * I 2)
      linarith
  · -- the sum over the three columns, entry by entry
    rw [PolyZonotope.isPolytopeCex_coraNormalCone I h, PolyZonotope.isPolytopeCex_coraVertex,
      PolyZonotope.isPolytopeCex_coraVertex]
    erw [Fin.sum_univ_three]
    funext i
    fin_cases i
    · show 2 * J 0 + J 1 - (2 * I 0 + I 1) = _
      simp [s1]
      linear_combination (-(2 * J 0 + J 1 - (2 * I 0 + I 1))) * q1
    · show J 0 * J 2 - I 0 * I 2 = _
      simp [s2]
      linear_combination (-(J 0 * J 2 - I 0 * I 2)) * q2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
