import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid
import CORALean.NN.Layers.Theorems.Real.TanhEqSigmoid

/-!
# tanh's derivative through the logistic function

`tanh' t = 4 σ'(2t)`: the conjugation identity differentiated, which is why the bracket the
sigmoid relaxation transports to tanh is tanh's own and not merely a sound one. Mathlib's own
`tanh` derivative is not what this reads.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem hasDerivAt_tanh (t : ℝ) :
    HasDerivAt Real.tanh (4 * sigmoidDeriv (2 * t)) t := by -- --- PROOF ---
  have hinner : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
    simpa using (hasDerivAt_id t).const_mul (2:ℝ)
  have hchain : HasDerivAt (fun s : ℝ => sigmoid (2 * s)) (sigmoidDeriv (2 * t) * 2) t :=
    (hasDerivAt_sigmoid (2 * t)).comp t hinner
  have h := (hchain.const_mul (2:ℝ)).sub_const (1:ℝ)
  -- the conjugating affine map, undone on the function and on the value alike
  rw [show (fun s : ℝ => 2 * sigmoid (2 * s) - 1) = Real.tanh from
      funext fun s => (tanh_eq_sigmoid s).symm,
    show 2 * (sigmoidDeriv (2 * t) * 2) = 4 * sigmoidDeriv (2 * t) by ring] at h
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
