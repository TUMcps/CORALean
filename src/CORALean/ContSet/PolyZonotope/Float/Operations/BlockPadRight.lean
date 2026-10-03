import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `PolyZonotope.blockPadRight` over a floating-point scalar

A set put into the last coordinates of a larger space, zero in the `n₁` above: the exact layer's
`map` at the embedding `blockPadRight`. A zero row has no rounding, so the centre, the generators
and the error box are only padded.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.blockPadRight (n₁ : ℕ) (pZ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 (n₁ + n) where
  p := pZ.p
  h := pZ.h
  q := pZ.q
  c := Fin.append (fun _ => zero) pZ.c
  G := fun i l => Fin.addCases (motive := fun _ => 𝕋) (fun _ => zero) (fun i => pZ.G i l) i
  E := pZ.E
  GI := fun i j => Fin.addCases (motive := fun _ => 𝕋) (fun _ => zero) (fun i => pZ.GI i j) i
  err := ⟨Fin.append (fun _ => zero) pZ.err.inf, Fin.append (fun _ => zero) pZ.err.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
