module

public import CORALean.ContSet.Taylm.Real.Operations.Reexpand
public import CORALean.ContSet.Taylm.Real.Operations.PolyBounds

@[expose] public section

/-!
# A polynomial's bounds over a box by re-expansion

The advanced setting of [1, Alg. 1]: re-expand `P` at the box's centre, scaled to the
normalized box, and bound the result there by interval arithmetic (`polyBounds`). CORA's
`optBnbAdv` bounds each sub-box this way.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.reexpBoxBounds (P : List (ℝ × (Fin n → ℕ))) (B : Fin n → Interval ℝ) :
    Interval ℝ :=
  Taylm.polyBounds (Taylm.reexpTerms (Taylm.boxMid B) (Taylm.boxRad B) P)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
