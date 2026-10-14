module

public import CORALean.ContSet.ConZonotope.Float.Operations.SupportBound
public import CORALean.ContSet.Conversion.Float.HPolytope_to_ConZonotopeInner
public import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
public import CORALean.ContSet.HPolytope.Float.Operations.MinkDiffOf
public import CORALean.ContSet.HPolytope.Float.Operations.RowLin
public import CORALean.ContDynamics.LinearSys.LinearSys

@[expose] public section

/-!
# `Alg. 2` line 11 in floats: one operand `CZ(P ⊖ Ẑ_W(τ_k))`, from the inside

[1, Alg. 2] line 11, of the maximal (EA) set, is `CZ ← conv(CZ(P₁ ⊖ Ẑ_W(τ_k)), CZ(P₂ ⊖
Ẑ_W(τ_k)))`; this is one operand, the hull is `maxBackReachStepFloat`'s. The numbering is arXiv
v1's, as in every file on this paper: v3 and the TAC version insert a conversion algorithm as
their `Alg. 1`, so this listing is their `Alg. 3`; their `Alg. 2` is the AE set, whose line 11
is `MinBackReachStepFloat`'s. The erosion (11) lowers each bound `d_(j)` by
`ρ(Ẑ_W(τ_k), H_(j,·)ᵀ)` rounded *up* (`ConZonotope.boundDot`, a check in ℚ, hence `ToRat 𝕋`),
so it is inside the exact eroded polytope. The conversion (17) (v3's `Alg. 1`) is
`HPolytope.conZonotopeInner`, inner where the paper's is exact, at the caller's box `Bx`, which
decides only how much of the polytope the result covers, never whether it stays inside.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
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

/-- [1, Alg. 2] line 11, one operand: `CZ(P ⊖ Ẑ_W(τ_k))` at the conversion box `Bx`, inside the
exact eroded polytope. -/
def LinearSys.maxBackReachCZFloat (Bx : Interval (Vec 𝕋 n)) (P : HPolytope 𝕋 (Vec 𝕋 n))
    (ZW : Zonotope (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  let ρ_ZW : ∀ j, FloatBound 𝕋 ZW.construct (rowLin P.A j) := fun j =>   -- ρ(Ẑ_W, H_(j,·)ᵀ)
    let u := ZW.conZonotope.boundDot (c := rowLin P.A j) (P.A j) fun _ => rfl
    ⟨u.val, fun x hx => u.le x (Zonotope.conZonotope_contains ZW hx)⟩
  let P_ZW := P.minkDiffOf ZW.construct ρ_ZW                        -- 11. P ⊖ Ẑ_W(τ_k), (11)
  P_ZW.conZonotopeInner Bx                                          -- 11. CZ(P ⊖ Ẑ_W(τ_k)), (17)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
