module

public import CORALean.ContDynamics.LinProbSys.Operations.InitReach
public import CORALean.ContDynamics.LinProbSys.Theorems.InputCovEq

@[expose] public section

/-!
# `initReach` hands `post` the noise covariance of one step

For a diagonalizable `A = V diag(λ) V⁻¹` given as its eigendecomposition, the probabilistic
input solution `pRinput` of `initReach` carries the noise covariance `Σ_s(r)` of one step
exactly (`inputCov_eq_noiseCovariance`), and the probabilistic particular solution it starts
`post` from, `zonotope(pRinput)`, a set, the covariance `0 = Σ_s(0)`: the noise of the first step
enters `Rfirst` and `options` only as the `gamma`-confidence set, as in [1, Alg. 1]. These are
the two hypotheses of `post_cov`. Covariances only: nothing here says that a probabilistic
zonotope encloses the law of the process.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinProbSys.initReach_cov (sys : LinProbSys n m) (Veig : Mat ℝ n n)
    (lambda : Fin n → ℝ) (hV : IsUnit Veig.det) (hA : sys.A = Veig * diagonal lambda * Veig⁻¹)
    (Rinit : ProbZonotope n) (gammaInit : ℝ) (U : Zonotope (Vec ℝ m)) (uTrans : Vec ℝ m)
    (r : ℝ) (η : ℕ) (gamma : ℝ) (originContained : Bool) : -- --- STMT ---
    (sys.initReach Veig lambda Rinit gammaInit U uTrans r η gamma originContained).2.2.2.cov
        = noiseCovariance sys.A sys.C r ∧
      (sys.initReach Veig lambda Rinit gammaInit U uTrans r η gamma
          originContained).2.2.1.Rpar_prob.cov
        = noiseCovariance sys.A sys.C 0 := by -- --- PROOF ---
  refine ⟨LinProbSys.inputCov_eq_noiseCovariance sys.A Veig lambda hV hA sys.C r, ?_⟩
  funext i j
  simp [LinProbSys.initReach, noiseCovariance]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
