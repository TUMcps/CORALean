module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.blockPadRight` over a floating-point scalar

A set put into the last coordinates of a larger space, zero in the `n₁` above: the exact layer's
`map` at the embedding `blockPadRight`. A zero row has no rounding, so the center, the generators
and the error box are only padded.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.blockPadRight (n₁ : ℕ) (pZ : PolyZonotope (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 (n₁ + n)) where
  p := pZ.p
  h := pZ.h
  q := pZ.q
  c := Fin.append (fun _ => zero) pZ.c
  G := fun l => Fin.append (fun _ => zero) (pZ.G l)
  E := pZ.E
  GI := fun j => Fin.append (fun _ => zero) (pZ.GI j)
  I_error := ⟨Fin.append (fun _ => zero) pZ.I_error.inf, Fin.append (fun _ => zero) pZ.I_error.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
