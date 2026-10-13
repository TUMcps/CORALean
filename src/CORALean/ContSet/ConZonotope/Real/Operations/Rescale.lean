import CORALean.ContSet.ConZonotope.Real.Operations.OfMat

/-!
# `ConZonotope.rescale`

CORA's `conZonotope/rescale` and [1, Prop. 4]'s eq. 24: the coefficient box `[ξL, ξU]` is
mapped back onto `[-1, 1]` by `ξ = ξm + diag(ξr) δ`, changing the representation and not the set.
The interval is an argument. CORA computes it by `2 n_g` linear programs (`'exact'`, eqs. 25-26)
or by Gauss-Jordan preconditioning and Algorithm 1 (`'iter'`); neither is part of this
operation, and the printed `R` rescaling (A.3) is not kept.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 4]: `{G diag(ξr), c + G ξm, A diag(ξr), b − A ξm}`. -/
noncomputable def ConZonotope.rescale {q h : ℕ} (c : α) (G : Fin h → α) (A : Mat ℝ q h)
    (b : Vec ℝ q) (ξL ξU : Vec ℝ h) : ConZonotope α :=
  let ξm : Vec ℝ h := fun j => (ξU j + ξL j) / 2               -- ξm = ½(ξU + ξL)
  let ξr : Vec ℝ h := fun j => (ξU j - ξL j) / 2               -- ξr = ½(ξU − ξL)
  ConZonotope.ofMat (c + ∑ j, ξm j • G j) (fun j => ξr j • G j)
    (A * Matrix.diagonal ξr) (b - A *ᵥ ξm)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
