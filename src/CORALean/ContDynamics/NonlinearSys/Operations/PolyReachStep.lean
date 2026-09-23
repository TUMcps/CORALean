import CORALean.ContDynamics.LinearSys.Operations.PostDelta
import CORALean.ContDynamics.NonlinearSys.Definitions.PolyReach
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainder
import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
import CORALean.ContDynamics.NonlinearSys.Operations.VarInputs
import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep

/-!
# `Alg. 1` lines 3-16: one iteration of the main loop

[1, Alg. 1]'s step. Lines 4-10, the repeat-enlarge-until loop picking the
abstraction error, are `abstrErrLoop` — the very loop [1] introduces, later
renumbered by the HSCC'21 and NAHS'22 papers' own `Alg. 1`.

`taylor` (line 3) stands for the derivative bundle `(z✱, A, w, B, D, E)` no
automatic differentiation here computes, as `CentreAbstrStep`'s own `lin`
stands for `taylor`'s first two. `combine` is `×` (lines 9, 11-12) at the
*stacked* dimension `D`/`E` are sized for, matching how `VarInputsOuter`
already takes that pairing as a hypothesis rather than a construction. `post`
(line 13) is the paper's own combination step, distinct from `post∆`
(`postDelta`, line 6) and not itself in this tree; `sub`/`enlarge` are
`abstrErrLoop`'s own parameters, as at its other callers. Line 7's one-argument
`CH(R(ts)) ⊕ R∆(τs))` is read as `CH(R(ts), R(ts) ⊕ R∆(τs))`, the "start
point, one step ahead" hull every other reach algorithm here uses.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       21-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Real.OfInterval

variable {n m o : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-16: one iteration of [1, Alg. 1]'s main loop; `none` where fuel ran out before
lines 4-10's loop found a fixed point. -/
noncomputable def NonlinearSys.polyReachStep (U UΔ : PolyZonotope (Vec ℝ m))
    (taylor : NonlinearSys.PolyTaylor n m o) (combine : PolyZonotope (Vec ℝ n) →
      PolyZonotope (Vec ℝ m) → PolyZonotope (Vec ℝ o)) (post : NonlinearSys.PolyPost n m o)
    (sub : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n) → Bool)
    (enlarge : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n)) (r : ℝ) (η fuel : ℕ)
    (s : NonlinearSys.PolyReachState n) : Option (NonlinearSys.PolyReachState n) :=
  let (zStar, A, w, B, D, E) := taylor s.R                            -- 3. taylor
  let lsys : LinearSys ℝ n := NonlinearSys.linearize A                -- 3. the linearized A
  -- lines 6-9, at whichever `Ω` lines 4-10's loop is currently trying
  let Φ : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n) := fun Ω =>
    let RΔτ := lsys.postDelta (S := 𝒫𝒵) r η s.R Ω                     -- 6. R∆(τs), post∆
    let Rτ := PolyZonotope.linComb s.R (s.R ⊞ RΔτ)                    -- 7. R(τs) = CH(R(ts), ·)
    let RτU := combine Rτ U                                           -- 9. R(τs) × U
    let L := lagrangeRemainder E RτU.zonotope zStar                   -- 8. L(s)
    let sqDRτU := PolyZonotope.quadMapDep D RτU                       -- 9. sq(D, R(τs)×U)
    ((PolyZonotope.ofPoint w).plus (PolyZonotope.mtimes B UΔ)).plus
      ((PolyZonotope.map ((2 : ℝ)⁻¹ • LinearMap.id) sqDRτU).plus
        (Real.OfInterval.ofInterval (S := 𝒫𝒵) L))                     -- 9. w ⊕ BUΔ ⊕ ½sq(D,·) ⊕ L
  match abstrErrLoop (S := 𝒫𝒵) sub enlarge Φ s.Ω fuel with             -- 4.-10. repeat...until
  | none => none
  | some Ω =>
    let RΔτ := lsys.postDelta (S := 𝒫𝒵) r η s.R Ω                     -- 6. at the fixed point
    let Rτ := PolyZonotope.linComb s.R (s.R ⊞ RΔτ)                    -- 7. R(τs)
    let RzTs := combine s.R U                                         -- 11. Rz(ts) = R(ts) × U
    let RΔzτs := combine RΔτ UΔ                                       -- 11. R∆z(τs) = R∆(τs) × UΔ
    let VΔτs := varInputs B D RzTs RΔzτs UΔ                           -- 12. V∆(τs)
    let L := lagrangeRemainder E (combine Rτ U).zonotope zStar        -- 14. L(τs)
    let Rts1 := post s.R RzTs w A B D VΔτs L                          -- 13. R(t_{s+1})
    some { t := s.t + r, R := Rts1, Rτ := Rτ, Ω := Ω }                -- 15.-16. t, s advance

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
