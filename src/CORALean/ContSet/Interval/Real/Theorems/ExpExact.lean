import CORALean.ContSet.Interval.Real.Operations.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `Interval.exp` is exactly the image under the exponential

`exp` is a strictly increasing bijection onto `(0, ∞)`, so a point of the new box has a logarithm,
and that logarithm lies in the old one. Needs no nonemptiness: a crossed box maps to a crossed
one.

[1, Eq. 4]: `e^[x] = [e^x̲, e^x̅]`.

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.exp_exact (I : Interval (Vec ℝ n)) :
    I.exp.construct = (fun x i => Real.exp (x i)) '' I.construct := by -- --- PROOF ---
  ext y
  constructor
  · intro hy
    have hy' : ∀ i, Real.exp (I.inf i) ≤ y i ∧ y i ≤ Real.exp (I.sup i) := fun i => hy i
    have hpos : ∀ i, 0 < y i := fun i => lt_of_lt_of_le (Real.exp_pos _) (hy' i).1
    refine ⟨fun i => Real.log (y i), fun i => ⟨?_, ?_⟩, funext fun i => Real.exp_log (hpos i)⟩
    · exact (Real.le_log_iff_exp_le (hpos i)).2 (hy' i).1
    · exact (Real.log_le_iff_le_exp (hpos i)).2 (hy' i).2
  · rintro ⟨x, hx, rfl⟩ i
    have hx' : I.inf i ≤ x i ∧ x i ≤ I.sup i := hx i
    exact ⟨Real.exp_le_exp.2 hx'.1, Real.exp_le_exp.2 hx'.2⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
