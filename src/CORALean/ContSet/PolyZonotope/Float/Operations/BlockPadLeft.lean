import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `PolyZonotope.blockPadLeft` over a floating-point scalar

A set put into the first coordinates of a larger space, zero in the `n₂` below: the exact layer's
`map` at the embedding `blockPadLeft`. A zero row has no rounding, so the centre, the generators and
the error box are only padded.
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

def PolyZonotope.blockPadLeft (n₂ : ℕ) (pZ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 (n + n₂) where
  p := pZ.p
  h := pZ.h
  q := pZ.q
  c := Fin.append pZ.c fun _ => zero
  G := fun i l => Fin.addCases (motive := fun _ => 𝕋) (fun i => pZ.G i l) (fun _ => zero) i
  E := pZ.E
  GI := fun i j => Fin.addCases (motive := fun _ => 𝕋) (fun i => pZ.GI i j) (fun _ => zero) i
  err := ⟨Fin.append pZ.err.inf fun _ => zero, Fin.append pZ.err.sup fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
