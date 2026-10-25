module

public import CORALean.ContDynamics.LinearSys.Operations.PostDelta
public import CORALean.ContDynamics.NonlinearSys.Definitions.PolyReach
public import CORALean.ContDynamics.NonlinearSys.Definitions.PolyReachOptions
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
public import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainder
public import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
public import CORALean.ContDynamics.NonlinearSys.Operations.VarInputs
public import CORALean.ContDynamics.Reach.Definitions.InputParams
public import CORALean.ContSet.Conversion.Real.Instances
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.OfPoint
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep

@[expose] public section

/-!
# `Alg. 1` line 18: the reachable set

`polyReachReach`: `R([0,t_f])`, the union of the first `K` iterations'
time-interval sets.

## Inputs
* `params` – reachability parameters
* `options` – reachability options

## Output
* the union of the time-interval sets

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative Polynomialization
      and Non-Convex Sets". Proceedings of the 16th international conference on Hybrid systems:
      computation and control, 2013.
-/

-- Authors:       Claude Sonnet 5
-- Written:       21-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n m o : ℕ}
open Matrix ContSet Real.OfInterval


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Line 1, before the first iteration. -/
def NonlinearSys.aux_polyReachInit (X₀ : PolyZonotope (Vec ℝ n)) : NonlinearSys.PolyReachState n :=
  { t := 0, R := X₀, Rτ := X₀, Ω := PolyZonotope.ofPoint 0 }    -- 1. t₀,s ← 0; Ω(0) ← {0}

/-- Lines 3-16: one iteration of [1, Alg. 1]'s main loop; `none` where fuel ran out before
lines 4-10's loop found a fixed point. -/
noncomputable def NonlinearSys.aux_polyReachStep (U UΔ : PolyZonotope (Vec ℝ m))
    (taylor : NonlinearSys.PolyTaylor n m o) (combine : PolyZonotope (Vec ℝ n) →
      PolyZonotope (Vec ℝ m) → PolyZonotope (Vec ℝ o)) (post : NonlinearSys.PolyPost n m o)
    (sub : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n) → Bool)
    (enlarge : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n)) (r : ℝ) (η fuel : ℕ)
    (s : NonlinearSys.PolyReachState n) : Option (NonlinearSys.PolyReachState n) :=
  -- 3. taylor
  let (zStar, A, w, B, D, E) := taylor s.R
  -- 3. the linearized A
  let lsys : LinearSys ℝ n := NonlinearSys.linearize A
  -- lines 6-9, at whichever `Ω` lines 4-10's loop is currently trying
  let Φ : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n) := fun Ω =>
    -- 6. R∆(τs), post∆
    let RΔτ := lsys.postDelta (S := 𝒫𝒵) r η s.R Ω
    -- 7. R(τs) = CH(R(ts), ·)
    let Rτ := PolyZonotope.linComb s.R (s.R ⊞ RΔτ)
    -- 9. R(τs) × U
    let RτU := combine Rτ U
    -- 8. L(s)
    let L := lagrangeRemainder E RτU.zonotope zStar
    -- 9. sq(D, R(τs)×U)
    let sqDRτU := PolyZonotope.quadMapDep D RτU
    -- 9. w ⊕ BUΔ ⊕ ½sq(D,·) ⊕ L
    ((PolyZonotope.ofPoint w).plus (PolyZonotope.mtimes B UΔ)).plus
      ((PolyZonotope.map ((2 : ℝ)⁻¹ • LinearMap.id) sqDRτU).plus
        (Real.OfInterval.ofInterval (S := 𝒫𝒵) L))
  -- 4.-10. repeat...until
  match abstrErrLoop (S := 𝒫𝒵) sub enlarge Φ s.Ω fuel with
  | none => none
  | some Ω =>
    -- 6. at the fixed point
    let RΔτ := lsys.postDelta (S := 𝒫𝒵) r η s.R Ω
    -- 7. R(τs)
    let Rτ := PolyZonotope.linComb s.R (s.R ⊞ RΔτ)
    -- 11. Rz(ts) = R(ts) × U
    let RzTs := combine s.R U
    -- 11. R∆z(τs) = R∆(τs) × UΔ
    let RΔzτs := combine RΔτ UΔ
    -- 12. V∆(τs)
    let VΔτs := varInputs B D RzTs RΔzτs UΔ
    -- 14. L(τs)
    let L := lagrangeRemainder E (combine Rτ U).zonotope zStar
    -- 13. R(t_{s+1})
    let Rts1 := post s.R RzTs w A B D VΔτs L
    -- 15.-16. t, s advance
    some { t := s.t + r, R := Rts1, Rτ := Rτ, Ω := Ω }

/-- Lines 2-17: iterate `aux_polyReachStep` while `t_s < t_f`; `none` past a step that ran out
of fuel. -/
noncomputable def NonlinearSys.aux_polyReachRun (U UΔ : PolyZonotope (Vec ℝ m))
    (taylor : NonlinearSys.PolyTaylor n m o) (combine : PolyZonotope (Vec ℝ n) →
      PolyZonotope (Vec ℝ m) → PolyZonotope (Vec ℝ o)) (post : NonlinearSys.PolyPost n m o)
    (sub : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n) → Bool)
    (enlarge : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n)) (r tf : ℝ) (η fuel : ℕ)
    (X₀ : PolyZonotope (Vec ℝ n)) : ℕ → Option (NonlinearSys.PolyReachState n)
  | 0 => some (NonlinearSys.aux_polyReachInit X₀)                          -- 1. initialize
  | k + 1 =>
    match NonlinearSys.aux_polyReachRun U UΔ taylor combine post sub enlarge r tf η fuel X₀ k with
    | none => none
    | some s =>
      if s.t < tf                                                     -- 2. while t_s < t_f
      then NonlinearSys.aux_polyReachStep U UΔ taylor combine post sub enlarge r η fuel s
      else some s


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] line 18: `R([0,t_f])`, the union of the first `K` iterations' time-interval
sets. The horizon is `params.tFinal - params.tStart`, the loop's clock starting at `0`. -/
noncomputable def NonlinearSys.polyReachReach
    (params : Reach.InputParams (PolyZonotope (Vec ℝ n)) (PolyZonotope (Vec ℝ m)) ℝ)
    (options : NonlinearSys.PolyReachOptions n m o) : Set (Vec ℝ n) :=
  let X₀ := params.X₀                                               -- the paper's symbols
  let U := params.U
  -- 2. the horizon of the loop, whose clock starts at `0`
  let tf := params.tFinal - params.tStart
  -- 18. `R([0,t_f])`, the union of the time-interval sets of iterations 1 to `K`
  ⋃ j < options.K, ⋃ s ∈ NonlinearSys.aux_polyReachRun U options.UΔ options.taylor options.combine
    options.post options.sub options.enlarge options.Δt tf options.η options.fuel
    X₀ (j + 1), construct s.Rτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
