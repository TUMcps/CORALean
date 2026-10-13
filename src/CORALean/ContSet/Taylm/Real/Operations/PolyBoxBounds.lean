module

public import CORALean.ContSet.Taylm.Real.Operations.TermBoxBounds

@[expose] public section

/-!
# A polynomial's bounds over a box by interval arithmetic

[1, Eq. 12]: each monomial's coordinates replaced by their intervals, the powers and products
taken in interval arithmetic, scaled by the coefficient, and summed. Over the normalized box this
is `polyBounds`; here the box is any, which is what branch and bound needs for its sub-boxes.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.polyBoxBounds (L : List (ℝ × (Fin n → ℕ))) (B : Fin n → ℝ × ℝ) :
    ℝ × ℝ :=
  ((L.map fun a => (Taylm.termBoxBounds B a).1).sum,
    (L.map fun a => (Taylm.termBoxBounds B a).2).sum)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
