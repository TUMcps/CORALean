import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Algebra.BigOperators.Fin

/-!
# `Zonotope.averagingWeights`

CORA's closed-form `'normGen'` weights of `priv_andAveraging`, [1, Prop. 1] Eq. 19:
`wʲ = 1 / (tr(Ḡʲ Ḡʲᵀ) Σᵣ 1 / tr(Ḡʳ Ḡʳᵀ))`, the weights of sum one that minimize the Frobenius
norm of the averaged zonotope's generators. `tr(Ḡ Ḡᵀ)` is the sum of the squared entries of
the generator matrix; a zonotope with no generators has trace zero and `1 / 0 = 0` in Lean, so
the weights are meaningful for generator matrices that are not zero.

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      360(10):6976-6993, 2023. arXiv:2003.10347.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.averagingWeights (Z : Fin N → Zonotope (Vec ℝ n)) : Fin N → ℝ :=
  let α : Fin N → ℝ := fun j => ∑ i, ∑ k, (Z j).G k i ^ 2    -- tr(Ḡʲ Ḡʲᵀ)
  fun j => (α j * ∑ r, (α r)⁻¹)⁻¹                              -- Eq. 19

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
