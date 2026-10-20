module

public import CORALean.ContDynamics.LinProbSys.Theorems.InitReachInputCov
public import CORALean.ContDynamics.LinProbSys.Theorems.PostCov

@[expose] public section

/-!
# From `initReach`, every `post` step carries the noise covariance

Starting from `initReach`'s `options` and running `post` `k` times with its `pRinput`, the
probabilistic particular solution has the covariance `Σ_s(k r)` of the noise accumulated over
`k` steps, and the time-interval set of the next step that of `r + k r`: `initReach_cov` gives
`post_cov` its two hypotheses, and `post_cov` the induction step. For a diagonalizable `A`
given as its eigendecomposition. Covariances only, not the law of the process.

## Inputs
* `sys` – system
* `Veig` – eigenvector matrix
* `lambda` – eigenvalues
* `Rinit` – initial probabilistic zonotope
* `gammaInit` – confidence level of the initial set
* `U` – input zonotope
* `uTrans` – constant input
* `r` – step size
* `η` – Taylor order
* `gamma` – confidence level
* `originContained` – input set holds the origin
* `k` – number of post steps

## Hypotheses
* `hV` – eigenvector matrix invertible
* `hA` – `Veig` and `lambda` diagonalize the matrix

## Conclusion
* after `k` post steps the covariances are the accumulated noise covariances
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

theorem LinProbSys.initReach_post_cov (sys : LinProbSys n m) (Veig : Mat ℝ n n)
    (lambda : Fin n → ℝ) (hV : IsUnit Veig.det) (hA : sys.A = Veig * diagonal lambda * Veig⁻¹)
    (Rinit : ProbZonotope n) (gammaInit : ℝ) (U : Zonotope (Vec ℝ m)) (uTrans : Vec ℝ m)
    (r : ℝ) (η : ℕ) (gamma : ℝ) (originContained : Bool) (k : ℕ) : -- --- CONCL ---
    ((fun st => (sys.post r (sys.initReach Veig lambda Rinit gammaInit U uTrans r η gamma
        originContained).2.2.2 st).1)^[k]
        (sys.initReach Veig lambda Rinit gammaInit U uTrans r η gamma
          originContained).2.2.1).Rpar_prob.cov = noiseCovariance sys.A sys.C (k * r) ∧
      (sys.post r (sys.initReach Veig lambda Rinit gammaInit U uTrans r η gamma
        originContained).2.2.2 ((fun st => (sys.post r (sys.initReach Veig lambda Rinit gammaInit
          U uTrans r η gamma originContained).2.2.2 st).1)^[k]
        (sys.initReach Veig lambda Rinit gammaInit U uTrans r η gamma
          originContained).2.2.1)).2.cov
        = noiseCovariance sys.A sys.C (r + k * r) := by -- --- PROOF ---
  obtain ⟨hp, h0⟩ := sys.initReach_cov Veig lambda hV hA Rinit gammaInit U uTrans r η gamma
    originContained
  set out := sys.initReach Veig lambda Rinit gammaInit U uTrans r η gamma originContained
  -- the state after `k` steps, by induction with `post_cov`
  have hk : ∀ k : ℕ, ((fun st => (sys.post r out.2.2.2 st).1)^[k] out.2.2.1).Rpar_prob.cov
      = noiseCovariance sys.A sys.C (k * r) := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      rw [Function.iterate_succ_apply',
        (sys.post_cov r (k * r) out.2.2.2 _ ih hp).1]
      push_cast
      ring_nf
  exact ⟨hk k, (sys.post_cov r (k * r) out.2.2.2 _ (hk k) hp).2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
