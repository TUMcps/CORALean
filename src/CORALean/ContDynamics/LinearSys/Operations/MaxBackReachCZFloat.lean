import CORALean.ContSet.ConZonotope.Float.Operations.SupportBound
import CORALean.ContSet.Conversion.Float.HPolytope_to_ConZonotopeInner
import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
import CORALean.ContSet.HPolytope.Float.Operations.MinkDiffOf
import CORALean.ContSet.HPolytope.Float.Operations.RowLin
import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# `Alg. 2` line 11 in floats: `CZ(P ⊖ Ẑ_W(τ_k))`, from the inside

`maxBackReachCZ` computed in `𝕋`: the polytope `P` eroded by the disturbance set `Ẑ_W(τ_k)` and
converted to a constrained zonotope by (17). The erosion is a guarantee, so the bound of each
inequality is lowered by the subtrahend's support in that row's direction, rounded *up*
(`HPolytope.minkDiffOf`), and the conversion is `HPolytope.conZonotopeInner`: the carried rows
tightened where the outer conversion widens them, no error box, so the result is inside the
eroded polytope. The box the conversion is taken at only decides how much of the polytope the
result covers, never whether it stays inside, and is the caller's, where the exact layer's
`ρ` hands in the supports of the bounding box.

The supports are computed, not supplied: the zonotope's through `ConZonotope.boundDot` (a
check in ℚ, hence `ToRat 𝕋`).
The lines are those of [1, Alg. 2].

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Line 11: `CZ(P ⊖ Ẑ_W(τ_k))` at the conversion box `Bx`, inside the exact eroded polytope. -/
def LinearSys.maxBackReachCZFloat (Bx : Interval (Vec 𝕋 n)) (P : HPolytope 𝕋 (Vec 𝕋 n))
    (ZW : Zonotope (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  let Q := P.minkDiffOf ZW.construct fun i =>                       -- ⊖ Ẑ_W(τ_k)
    let u := ZW.conZonotope.boundDot (c := rowLin P.A i) (P.A i) fun _ => rfl
    ⟨u.val, fun x hx => u.le x (Zonotope.conZonotope_contains ZW hx)⟩
  Q.conZonotopeInner Bx                                             -- CZ(·), from inside

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
