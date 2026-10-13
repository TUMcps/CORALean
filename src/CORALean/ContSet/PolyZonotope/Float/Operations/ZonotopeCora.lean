module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `PolyZonotope.zonotopeCora`, over a floating-point scalar

CORA's `@polyZonotope/zonotope` as it is written, as over ℝ: an all-even dependent generator is
halved and its other half moved into the centre, every other one kept whole, and the independent
generators appended. Halving is exact; the centre's sum is rounded down and the gap to the upward
rounding is added to the top of the error box, which is otherwise carried across.
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

def PolyZonotope.zonotopeCora (pZ : PolyZonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  -- the generator kept free: half of an all-even column, all of any other
  let G : Fin pZ.h → Vec 𝕋 n := fun l i =>
    if ∀ k, pZ.E k l % 2 = 0 then half (pZ.G l i) else pZ.G l i
  -- the share moved into the centre: the other half of an all-even column
  let s : Fin pZ.h → Vec 𝕋 n := fun l i =>
    if ∀ k, pZ.E k l % 2 = 0 then half (pZ.G l i) else zero
  -- c + sum(G(:,ind), 2)/2, rounded both ways
  let cLo : Vec 𝕋 n := fun i => addDown (pZ.c i) (sumDown fun l => s l i)
  let cHi : Vec 𝕋 n := fun i => addUp (pZ.c i) (sumUp fun l => s l i)
  { h := pZ.h + pZ.q
    c := cLo
    G := Fin.append G pZ.GI
    E := ⟨pZ.err.inf, fun i => addUp (pZ.err.sup i) (subUp (cHi i) (cLo i))⟩ }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
