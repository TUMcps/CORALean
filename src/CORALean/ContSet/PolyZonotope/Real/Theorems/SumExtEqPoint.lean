import CORALean.ContSet.PolyZonotope.Real.Operations.ExtG
import CORALean.ContSet.PolyZonotope.Real.Operations.ExtM
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap

/-!
# A point of the set as a single sum

The centre becomes generator zero at the all-zero exponent column, so the whole
point is one sum over the extended index. Stated pointwise rather than as a set
equality because the constrained representation needs it at a *fixed* factor
vector, which is also why it carries no `aux_` prefix.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the set as one sum, the centre being generator zero at the
all-zero exponent column. -/
theorem PolyZonotope.sum_ext_eq_point (S : PolyZonotope α) (a : Fin S.p → ℝ) :
    ∑ l, extM S a l • extG S l = S.c + ∑ i, monomial S.E a i • S.G i := by -- --- PROOF ---
  have h0 : extM S a 0 = 1 := by
    show ∏ k, a k ^ PolyZonotope.extE S k 0 = 1
    exact Finset.prod_eq_one fun k _ => by
      simp only [PolyZonotope.extE, Fin.cons_zero, pow_zero]
  have hG0 : extG S 0 = S.c := by
    simp only [PolyZonotope.extG, Fin.cons_zero]
  -- every other column is an original generator, shifted by the one the centre took
  have hsucc : ∀ i : Fin S.h,
      extM S a i.succ • extG S i.succ = monomial S.E a i • S.G i := by
    intro i
    have hm : extM S a i.succ = monomial S.E a i := by
      show ∏ k, a k ^ PolyZonotope.extE S k i.succ = ∏ k, a k ^ S.E k i
      exact Finset.prod_congr rfl fun k _ => by
        simp only [PolyZonotope.extE, Fin.cons_succ]
    have hg : extG S i.succ = S.G i := by
      simp only [PolyZonotope.extG, Fin.cons_succ]
    rw [hm, hg]
  rw [Fin.sum_univ_succ, h0, hG0, one_smul]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => hsucc i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
