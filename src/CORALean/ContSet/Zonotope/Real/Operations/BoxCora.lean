module

public import CORALean.ContSet.Zonotope.Real.Operations.BoxRadiusCora

@[expose] public section

/-!
# `Zonotope.boxCora`: `zonotope(interval(Z))` as CORA builds it

`@interval/zonotope.m` ends with `G = diag(r); Z = zonotope([c, G(:,r ~= 0)])`: the generators of
zero radius are dropped, so the box has one generator per coordinate of non-zero radius, in
order. Its centre is the centre of `Z`. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- `zonotope(interval(Z))`: `zonotope([c, G(:,r ~= 0)])` with `G = diag(r)`. -/
noncomputable def Zonotope.boxCora (Z : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  let nz := (List.finRange n).filter fun i => Z.boxRadiusCora i ≠ 0
  ⟨nz.length, Z.c, fun k => Z.boxRadiusCora (nz.get k) • (Pi.single (nz.get k) 1 : Fin n → ℝ)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
