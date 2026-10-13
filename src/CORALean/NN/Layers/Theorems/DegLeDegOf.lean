import CORALean.NN.Layers.Operations.PolyRelaxationFamilyDegOf

/-!
# Every neuron's degree is under its layer's

What padding needs, and what makes the common degree no restriction.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyRelaxationFamily.deg_le_degOf (F : PolyRelaxationFamily 𝕋)
    (t : OrderPattern n) (i : Fin n) : F.deg (t i) ≤ F.degOf t :=
  Finset.le_sup (f := fun j => F.deg (t j)) (Finset.mem_univ i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
