module

public import CORALean.Specification.STL.Operations.FormulaScale
public import CORALean.Specification.STL.Operations.SampToFormula
public import CORALean.Specification.STL.Theorems.ScaleOfPform

@[expose] public section

/-!
# A sampled time formula at step 1 scales to step c

`(s.toFormula 1).scale c = s.toFormula c`: the time step of a sampled time formula is the scale of
the unit step, which is how [1, Table 1]'s `c = 1` serves every `c`.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Samp.toFormula_scale (c : ℝ≥0) (s : STL.Samp X) :
    (s.toFormula 1).scale c = s.toFormula c := by -- --- PROOF ---
  induction s with
  | lit ϱ => exact STL.Formula.scale_ofPform c ϱ
  | not s ih => simp only [STL.Samp.toFormula, STL.Formula.scale, ih]
  | and s t ihs iht =>
    simp only [STL.Samp.toFormula, STL.Formula.and, STL.Formula.scale, ihs, iht]
  | or s t ihs iht => simp only [STL.Samp.toFormula, STL.Formula.scale, ihs, iht]
  | next s ih =>
    simp only [STL.Samp.toFormula, STL.Formula.next, STL.Formula.scale, STL.Formula.tt, ih, one_mul]
  | fin ϱ => simp only [STL.Samp.toFormula, STL.Formula.scale, STL.Formula.scale_ofPform, one_mul]
  | glob ϱ => simp only [STL.Samp.toFormula, STL.Formula.scale, STL.Formula.scale_ofPform, one_mul]


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
