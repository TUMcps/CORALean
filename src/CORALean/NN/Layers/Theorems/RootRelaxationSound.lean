import CORALean.NN.Layers.Operations.RootRelaxation
import CORALean.NN.Layers.Theorems.OfMonotoneSound

/-!
# The square root relaxation is sound

`sqrtDown` and `sqrtUp` bracket `Real.sqrt` at every stored value, whatever the fuel `p`,
and `Real.sqrt` is monotone.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem rootRelaxation_sound (p : ℕ) : (rootRelaxation (𝕋 := 𝕋) p).Sound Real.sqrt :=
  Relaxation.ofMonotone_sound (fun _ _ h => Real.sqrt_le_sqrt h)
    ⟨fun a => sqrtDown_le p a, fun a => le_sqrtUp p a⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
