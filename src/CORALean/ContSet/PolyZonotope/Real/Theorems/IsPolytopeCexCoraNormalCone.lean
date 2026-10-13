module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.IsPolytopeCexMonomial
public import CORALean.ContSet.PolyZonotope.Real.Operations.CoraNormalCone
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Normal cone columns of `isPolytopeCex`

At a corner `(a, b, c)` with no zero factor the columns are `-sign(a) (2, c)`,
`-sign(b) (1, 0)`, `-sign(c) (0, a)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

set_option simprocs false in
/-- The columns of `N` at a corner with no zero factor, as CORA's `aux_normalCone` computes them
(printed in the module docstring of `Operations/IsPolytopeCex`). -/
theorem PolyZonotope.isPolytopeCex_coraNormalCone (I : Fin 3 → ℝ) (h : ∀ i, I i ≠ 0) :
    PolyZonotope.isPolytopeCex.coraNormalCone I =
      ![(-(SignType.sign (I 0) : ℝ)) • (![2, I 2] : Vec ℝ 2),
        (-(SignType.sign (I 1) : ℝ)) • (![1, 0] : Vec ℝ 2),
        (-(SignType.sign (I 2) : ℝ)) • (![0, I 0] : Vec ℝ 2)] := by -- --- PROOF ---
  -- column `i` is a sum over the three generators, the `if` being the filter `E(i,k) > 0`
  have h2 := h 2
  have e2 : (⟨2, by decide⟩ : Fin 3) = 2 := rfl
  funext i
  unfold PolyZonotope.coraNormalCone
  simp only []
  rw [Finset.sum_filter]
  erw [Fin.sum_univ_three]
  fin_cases i
  all_goals
    simp only [PolyZonotope.isPolytopeCex, Fin.zero_eta, Fin.mk_one,
      PolyZonotope.isPolytopeCex_monomial]
  all_goals
    simp [h 0, h 1, h2, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, e2]
  -- what is left are equalities of the vectors inside the `•`
  all_goals
    congr 1
    funext j
    fin_cases j <;> simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
