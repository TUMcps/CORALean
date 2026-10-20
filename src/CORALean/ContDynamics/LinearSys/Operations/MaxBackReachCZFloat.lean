module

public import CORALean.ContSet.ConZonotope.Float.Operations.SupportBound
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotopeInner
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeConZonotopeContains
public import CORALean.ContSet.HPolytope.Float.Operations.MinkDiffOf
public import CORALean.ContSet.HPolytope.Float.Operations.RowLin
public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeConZonotopeContains

@[expose] public section

/-!
# `Alg. 3` line 11 in floats: one operand `CZ(P ⊖ Ẑ_W(τ_k))`, from the inside

[1, Alg. 3] line 11, of the EA set, is `CZ ← conv(CZ(P₁ ⊖ Ẑ_W(τ_k)), CZ(P₂ ⊖
Ẑ_W(τ_k)))`; this is one operand, the hull is `maxBackReachStepFloat`'s. The erosion (11) lowers
each bound `d_(j)` by `ρ(Ẑ_W(τ_k), H_(j,·)ᵀ)` rounded *up* (`ConZonotope.boundDot`, a check in ℚ,
hence `ToRat 𝕋`), so it is inside the exact eroded polytope. The conversion [1, Alg. 1] is
`HPolytope.conZonotopeInner`, inner where the paper's is exact, at the caller's box `Bx`, which
decides only how much of the polytope the result covers, never whether it stays inside.

## Inputs
* `Bx` – conversion box
* `P` – float polytope
* `ZW` – float disturbance zonotope

## Output
* constrained zonotope inside the eroded polytope

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3] line 11, one operand: `CZ(P ⊖ Ẑ_W(τ_k))` at the conversion box `Bx`, inside the
exact eroded polytope. -/
def LinearSys.maxBackReachCZFloat (Bx : Interval (Vec 𝕋 n)) (P : HPolytope 𝕋 (Vec 𝕋 n))
    (ZW : Zonotope (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  let ρ_ZW : ∀ j, FloatBound 𝕋 ZW.construct (rowLin P.A j) := fun j =>   -- ρ(Ẑ_W, H_(j,·)ᵀ)
    let u := ZW.conZonotope.boundDot (c := rowLin P.A j) (P.A j) fun _ => rfl
    ⟨u.val, fun x hx => u.le x (Zonotope.conZonotope_contains ZW hx)⟩
  -- 11. P ⊖ Ẑ_W(τ_k), (11)
  let P_ZW := P.minkDiffOf ZW.construct ρ_ZW
  -- 11. CZ(P ⊖ Ẑ_W(τ_k)), Alg. 1
  P_ZW.conZonotopeInner Bx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
