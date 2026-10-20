module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.blockPadLeft` over a floating-point scalar

A set put into the first coordinates of a larger space, zero in the `n₂` below: the exact layer's
`map` at the embedding `blockPadLeft`. A zero row has no rounding, so the center, the generators and
the error box are only padded.

## Inputs
* `n₂` – number of appended zero coordinates
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope padded with zero coordinates on the right
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.blockPadLeft (n₂ : ℕ) (pZ : PolyZonotope (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 (n + n₂)) where
  p := pZ.p
  h := pZ.h
  q := pZ.q
  c := Fin.append pZ.c fun _ => zero
  G := fun l => Fin.append (pZ.G l) fun _ => zero
  E := pZ.E
  GI := fun j => Fin.append (pZ.GI j) fun _ => zero
  I_error := ⟨Fin.append pZ.I_error.inf fun _ => zero, Fin.append pZ.I_error.sup fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
