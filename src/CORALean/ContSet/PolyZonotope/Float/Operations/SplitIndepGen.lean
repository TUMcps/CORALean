import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `PolyZonotope.splitIndepGen`, over a floating-point scalar

The independent branch of `aux_splitLongestGen_` in CORA's `@polyZonotope/contains_`: the
independent generator `j` halved, one half with centre `c + GI(:,j)/2`, the other with
centre `c - GI(:,j)/2`. Halving is exact; the two centres are rounded down and the gap to the
upper rounding is added to the top of each error box.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two halves of `pZ` along its independent generator `j`. -/
def PolyZonotope.splitIndepGen (pZ : PolyZonotope (Vec 𝕋 n)) (j : Fin pZ.q) :
    PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n) :=
  -- GI(:,ind) = 0.5*GI(:,ind)
  let g : Vec 𝕋 n := fun i => half (pZ.GI j i)
  let GI' : Fin pZ.q → Vec 𝕋 n := Function.update pZ.GI j g
  -- c1 = c + 0.5*GI(:,ind), c2 = c - 0.5*GI(:,ind), rounded down
  let c₁ : Vec 𝕋 n := fun i => addDown (pZ.c i) (g i)
  let c₂ : Vec 𝕋 n := fun i => subDown (pZ.c i) (g i)
  -- the rounding gaps, on top of the error boxes
  let err₁ : Interval (Vec 𝕋 n) :=
    ⟨pZ.err.inf, fun i => addUp (pZ.err.sup i) (subUp (addUp (pZ.c i) (g i)) (c₁ i))⟩
  let err₂ : Interval (Vec 𝕋 n) :=
    ⟨pZ.err.inf, fun i => addUp (pZ.err.sup i) (subUp (subUp (pZ.c i) (g i)) (c₂ i))⟩
  (⟨pZ.p, pZ.h, pZ.q, c₁, pZ.G, pZ.E, GI', err₁⟩, ⟨pZ.p, pZ.h, pZ.q, c₂, pZ.G, pZ.E, GI', err₂⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
