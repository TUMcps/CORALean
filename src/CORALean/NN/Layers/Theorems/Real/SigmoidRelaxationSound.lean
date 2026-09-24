import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid
import CORALean.NN.Layers.Theorems.OfDerivSound
import CORALean.NN.Layers.Theorems.OfMonotoneSound
import CORALean.NN.Layers.Theorems.Real.EnclosureExactSound
import CORALean.NN.Layers.Theorems.Real.LeSigmoidDerivHi
import CORALean.NN.Layers.Theorems.Real.SigmoidDerivLoLe
import CORALean.NN.Layers.Theorems.TighterSound

/-!
# The sigmoid relaxation over ℝ is sound

ℝ-only, the relaxation being built at `σ` itself: the generic constructors' soundness at the
exact enclosure and the exact bracket, the clamped secant landing in the bracket by `max`/`min`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidRelaxation_sound : sigmoidRelaxation.Sound sigmoid := by -- --- PROOF ---
  -- the curvature half: the exact bracket, and the clamped secant inside it
  have hcurv : sigmoidCurvatureRelaxation.Sound sigmoid :=
    Relaxation.ofDeriv_sound sigmoidDeriv hasDerivAt_sigmoid (enclosure_exact_sound sigmoid)
      (fun _ _ _ h₁ h₂ => sigmoidDerivLo_le h₁ h₂) (fun _ _ _ h₁ h₂ => le_sigmoidDerivHi h₁ h₂)
      fun l u h => ⟨le_max_left _ _,
        max_le (le_trans (sigmoidDerivLo_le le_rfl h) (le_sigmoidDerivHi le_rfl h))
          (min_le_left _ _)⟩
  exact Relaxation.tighter_sound hcurv
    (Relaxation.ofMonotone_sound sigmoid_mono (enclosure_exact_sound sigmoid))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
