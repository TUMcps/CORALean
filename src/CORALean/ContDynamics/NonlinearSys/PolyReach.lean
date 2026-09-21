import CORALean.ContDynamics.LinearSys.Operations.PostDelta
import CORALean.ContDynamics.NonlinearSys.NonlinearSys
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainder
import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
import CORALean.ContDynamics.NonlinearSys.Operations.VarInputs
import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.PolyZonotope.Real.Instances
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep

/-!
# `Alg. 1`: reachability by conservative polynomialization

[1, Alg. 1]: lines 3-16 are `polyReachStep`, the loop of lines 2, 17 is `polyReachRun`, and line
18's union is `polyReachReach`, shaped as `CentreAbstrReach.lean` shapes its own `Alg. 1`. Lines
4-10, the repeat-enlarge-until loop picking the abstraction error, are `abstrErrLoop` — the very
loop [1] introduces, later renumbered by the HSCC'21 and NAHS'22 papers' own `Alg. 1`.

`taylor` (line 3) stands for the derivative bundle `(z✱, A, w, B, D, E)` no automatic
differentiation here computes, as `CentreAbstrStep`'s own `lin` stands for `taylor`'s first two.
`combine` is `×` (lines 9, 11-12) at the *stacked* dimension `D`/`E` are sized for, matching how
`VarInputsOuter` already takes that pairing as a hypothesis rather than a construction. `post`
(line 13) is the paper's own combination step, distinct from `post∆` (`postDelta`, line 6) and not
itself in this tree; `sub`/`enlarge` are `abstrErrLoop`'s own parameters, as at its other callers.

One reading choice: line 7's one-argument `CH(R(ts)) ⊕ R∆(τs))` is read as `CH(R(ts), R(ts) ⊕
R∆(τs))`, the "start point, one step ahead" hull every other reach algorithm here uses, a
one-argument hull being no widening at all. Line 13's argument list runs onto line 14 in the
source; both are one call, `L(τs)` line 8's `L(s)` recomputed at the fixed point.

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

/-- `taylor`, line 3: the expansion point over the stacked `(x, u)`, and the derivative
bundle `A, w, B, D, E` no automatic differentiation here computes. -/
abbrev NonlinearSys.PolyTaylor (n m o : ℕ) := PolyZonotope (Vec ℝ n) →
  Vec ℝ o × Mat ℝ n n × Vec ℝ n × Mat ℝ n m × (Fin n → Mat ℝ o o) × (Fin n → Fin o → Mat ℝ o o)

/-- `post`, line 13: `R(ts), Rz(ts), w, A, B, D, V∆(τs), L(τs) ↦ R(t_{s+1})`. -/
abbrev NonlinearSys.PolyPost (n m o : ℕ) := PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ o) →
  Vec ℝ n → Mat ℝ n n → Mat ℝ n m → (Fin n → Mat ℝ o o) → PolyZonotope (Vec ℝ n) →
  Real.Interval (Vec ℝ n) → PolyZonotope (Vec ℝ n)

/-- What one iteration of [1, Alg. 1] hands the next: `t_s`, `R(t_s)`, `R(τs)` (line 14's
last reduction, kept for the union), and the running abstraction-error guess `Ω`, seeded
once at line 1 and carried on past line 9. -/
structure NonlinearSys.PolyReachState (n : ℕ) where
  /-- `t_s`, line 16. -/
  t : ℝ
  /-- `R(t_s)`, lines 1, 6, 11, 13. -/
  R : PolyZonotope (Vec ℝ n)
  /-- `R(τs)`, line 7, for `R_union` at line 15. -/
  Rτ : PolyZonotope (Vec ℝ n)
  /-- `Ω(s)`, lines 1, 5, 9-10. -/
  Ω : PolyZonotope (Vec ℝ n)

/-- Line 1, before the first iteration. -/
def NonlinearSys.polyReachInit (X₀ : PolyZonotope (Vec ℝ n)) : NonlinearSys.PolyReachState n :=
  { t := 0, R := X₀, Rτ := X₀, Ω := PolyZonotope.ofPoint 0 }    -- 1. t₀,s ← 0; Ω(0) ← {0}

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

/-- Lines 2-17: iterate `polyReachStep` while `t_s < t_f`; `none` past a step that ran out
of fuel. -/
noncomputable def NonlinearSys.polyReachRun (U UΔ : PolyZonotope (Vec ℝ m))
    (taylor : NonlinearSys.PolyTaylor n m o) (combine : PolyZonotope (Vec ℝ n) →
      PolyZonotope (Vec ℝ m) → PolyZonotope (Vec ℝ o)) (post : NonlinearSys.PolyPost n m o)
    (sub : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n) → Bool)
    (enlarge : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n)) (r tf : ℝ) (η fuel : ℕ)
    (X₀ : PolyZonotope (Vec ℝ n)) : ℕ → Option (NonlinearSys.PolyReachState n)
  | 0 => some (NonlinearSys.polyReachInit X₀)                          -- 1. initialize
  | k + 1 =>
    match NonlinearSys.polyReachRun U UΔ taylor combine post sub enlarge r tf η fuel X₀ k with
    | none => none
    | some s =>
      if s.t < tf                                                     -- 2. while t_s < t_f
      then NonlinearSys.polyReachStep U UΔ taylor combine post sub enlarge r η fuel s
      else some s


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] line 18: `R([0,t_f])`, the union of the first `K` iterations' time-interval
sets. -/
noncomputable def NonlinearSys.polyReachReach (U UΔ : PolyZonotope (Vec ℝ m))
    (taylor : NonlinearSys.PolyTaylor n m o) (combine : PolyZonotope (Vec ℝ n) →
      PolyZonotope (Vec ℝ m) → PolyZonotope (Vec ℝ o)) (post : NonlinearSys.PolyPost n m o)
    (sub : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n) → Bool)
    (enlarge : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n)) (r tf : ℝ) (η fuel K : ℕ)
    (X₀ : PolyZonotope (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ j < K, ⋃ s ∈ NonlinearSys.polyReachRun U UΔ taylor combine post sub enlarge r tf η fuel
    X₀ (j + 1), construct s.Rτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
