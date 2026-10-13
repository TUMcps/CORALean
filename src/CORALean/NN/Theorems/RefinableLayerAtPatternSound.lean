import CORALean.NN.Layers.Instances
import CORALean.NN.Operations.RefinableLayerAtPattern

/-!
# Every pattern's layer is sound

At the refinable layer's own `eval`, whatever the pattern: the obligation is stored once and
asked at each.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem RefinableLayer.atPattern_sound (L : RefinableLayer S n m) (t : OrderPattern n) :
    (Enclose.toLayer (S := S) (L.atPattern t)).Sound L.eval :=
  ⟨L.enclose_outer t⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
