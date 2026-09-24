import CORALean.NN.Definitions.RefinableLayer
import CORALean.NN.Layers.Definitions.SoundLayer

/-!
# The layer a pattern names

Reading one pattern off a refinable layer gives a `SoundLayer`: the layer's `eval`, its
`enclose` at that pattern and the guarantee it already carries, which is what a network holds.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layer a pattern names, which is the only thing a network ever runs. -/
def RefinableLayer.atPattern (L : RefinableLayer S n m) (t : OrderPattern n) :
    SoundLayer S n m where
  eval := Erased.mk L.eval
  enclose := L.enclose t
  enclose_outer s := by
    rw [Erased.out_mk]
    rintro _ ⟨x, hx, rfl⟩
    exact L.enclose_outer t s x hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
