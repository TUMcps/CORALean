module

public import CORALean.ContSet.Taylm.Float.Operations.BernsteinEntryBounds
public import CORALean.ContSet.Taylm.Float.Operations.BoundsProd

@[expose] public section

/-!
# `Taylm.bernsteinCoeffBounds`

The Bernstein coefficient at `β` of a float term list, between two floats: each term's coefficient
times the entry brackets of its exponents, by `boundsProd`, then the lower ends summed down and the
upper ends summed up.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.bernsteinCoeffBounds (L : List (𝕋 × (Fin n → ℕ))) (N : ℕ) (β : Fin n → Fin (N + 1)) :
    𝕋 × 𝕋 :=
  let term : 𝕋 × (Fin n → ℕ) → 𝕋 × 𝕋 := fun a => Taylm.boundsProd
    (fun k => Taylm.bernsteinEntryBounds (𝕋 := 𝕋) N (a.2 k) (β k)) (List.finRange n) (a.1, a.1)
  (listSumDown (L.map fun a => (term a).1), listSumUp (L.map fun a => (term a).2))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
