module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.replaceId`, over a floating-point scalar

CORA's `@polyZonotope/replaceId`: factors are renamed by a map `f : Fin p → Fin p'`, the exponent
row of a new factor being the sum of the rows of the factors sent to it (natural numbers, so
exact). Centre, generators and error box are copied; nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factors renamed by `f`, the exponent rows of factors with a common new name added. -/
def PolyZonotope.replaceId (pZ : PolyZonotope (Vec 𝕋 n)) {p' : ℕ} (f : Fin pZ.p → Fin p') :
    PolyZonotope (Vec 𝕋 n) where
  p := p'
  h := pZ.h
  q := pZ.q
  c := pZ.c
  G := pZ.G
  E := fun k' i => ∑ k ∈ Finset.univ.filter (fun k => f k = k'), pZ.E k i
  GI := pZ.GI
  I_error := pZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
