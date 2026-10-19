module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# The member of a float bundle CORA's `zonotope(zB)` returns

`@zonoBundle/zonotope.m` returns the member of least box volume `prod(sum(abs(G), 2))`, the first
one where several tie. Here the volume is the product of the rows' `radius`, every operation
rounded up; the comparison only chooses a member, and every member encloses the bundle, so the
rounding cannot cost soundness.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's choice in `zonotope(zB)`: the first member of least box volume. -/
def ZonoBundle.minVolIdx (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) : Fin zB.k :=
  -- `vol(i) = prod(sum(abs(zB.Z{i}.G), 2))`
  let vol : Fin zB.k → 𝕋 := fun i =>
    Fin.foldl n (fun p r => mulUp p (radius (fun r j => (zB.Z i).G j r) r)) one
  -- `[~, minIdx] = min(vol)`: the first index of least volume
  (List.finRange zB.k).foldl (fun b i => if le (vol b) (vol i) then b else i) ⟨0, hk⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
