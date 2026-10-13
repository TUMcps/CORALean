import CORALean.NN.Layers.Definitions.SoundLayer

/-!
# Packing a layer of any kind

A layer of any `Enclose` kind, of any universe, as a `SoundLayer`: the three fields read off
the instance, so nothing is lost but the kind.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

universe u

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Enclose.pack {L : ℕ → ℕ → Type u} [Enclose L S] (l : L n m) : SoundLayer S n m where
  eval := Enclose.eval (S := S) l
  enclose := Enclose.enclose l
  enclose_outer := Enclose.enclose_outer l

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
