import CORALean.NN.Layers.Definitions.EvalPoly

/-!
# Mathlib's polynomials read as coefficients

ℝ-only, as `evalPoly` is: coefficients indexed by degree, up to the natural degree.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem evalPoly_coeff (p : Polynomial ℝ) (t : ℝ) :
    evalPoly (fun i : Fin (p.natDegree + 1) => p.coeff (i : ℕ)) t = Polynomial.eval t p := by
  rw [Polynomial.eval_eq_sum_range]
  exact Fin.sum_univ_eq_sum_range (fun i => p.coeff i * t ^ i) (p.natDegree + 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
