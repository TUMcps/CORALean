module

public import CORALean.NN.Definitions.RefinableLayer
public import CORALean.NN.Layers.Definitions.Basic

@[expose] public section

/-!
# A layer with nothing to spend

Every pattern is the layer itself, which is how a linear layer sits in a refinable network; its
soundness is the refinable layer's stored obligation.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A layer with nothing to spend: every pattern is the layer itself, which is
how a linear layer sits in a refinable network. -/
def Layer.refinable (L : Layer S n m) {f : Vec ℝ n → Vec ℝ m} (hf : L.Encloses f) :
    RefinableLayer S n m where
  eval := f
  enclose _ := L.enclose
  enclose_outer _ := hf.enclose_outer

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
