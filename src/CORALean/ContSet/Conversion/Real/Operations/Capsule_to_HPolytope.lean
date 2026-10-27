module

public import CORALean.ContSet.Capsule.Real.Operations.SupportBound
public import CORALean.ContSet.Conversion.Real.Definitions.GramSchmidt
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_HPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.EmptySet
public import CORALean.ContSet.HPolytope.Real.Operations.Eqs
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Real.Operations.Intersection
public import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Real.Operations.OfPoint
public import CORALean.ContSet.HPolytope.Real.Operations.Translate
public import CORALean.Global.StepOf

@[expose] public section

/-!
# A capsule as halfspaces, as CORA's `polytope(C)` dispatches

`@capsule/polytope.m`: an empty capsule gives the empty polytope; at `n = 1` the interval
`[c - |g| - r, c + |g| + r]` (`aux_1D`); a point its own polytope; a segment (`r = 0`) the rows
`±B(:,1)ᵀ x ≤ ‖g‖₂` and `B(:,2:end)ᵀ x = 0` shifted to `c` (`aux_exactLineConversion`); otherwise,
at `'outer'`, the rows `[B'; -B']` at the capsule's support value (`step_supportFunction`), with
`B = gramSchmidt(g)`. Departures: a negative radius is CORALean's empty capsule; the support value
is `⟨a, c⟩ + |⟨a, g⟩| + r ‖a‖₂` (`Capsule.supportBound`); a ball takes the identity for `B`, where
CORA's `gramSchmidt` divides by zero. CORA's default `'exact'` throws (`CORA:noExactAlg`) and
`'inner'` always throws, so this is `'outer'`.

## Inputs
* none

## Output
* halfspace polytope of the capsule, branch by branch
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Classical

variable {m : ℕ}


/-- CORA's `aux_exactLineConversion`: `±B(:,1)ᵀ x ≤ ‖g‖₂`, `B(:,2:end)ᵀ x = 0`, then `+ c`. -/
noncomputable def Capsule.hPolytopeOfLine (C : Capsule (m + 1)) :
    HPolytope (Vec ℝ (m + 1)) :=
  let B := gramSchmidtVec C.g
  let ineqs := HPolytope.ineqs ![Bᵀ 0, -Bᵀ 0] ![‖C.g‖₂, ‖C.g‖₂]
  let eqs := HPolytope.eqs (fun l => Bᵀ l.succ) 0
  HPolytope.translate C.c (ineqs.intersection eqs)


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The basis of `step_supportFunction`: `gramSchmidt(g)`, the identity at `g = 0`. -/
@[step_of Capsule.hPolytope]
noncomputable def Capsule.step_basis (C : Capsule (m + 1)) : Mat ℝ (m + 1) (m + 1) :=
  if C.g = 0 then 1 else gramSchmidtVec C.g

/-- CORA's `step_supportFunction`: the rows `[B'; -B']`, each at its support value. -/
noncomputable def Capsule.hPolytopeOuter (C : Capsule (m + 1)) :
    HPolytope (Vec ℝ (m + 1)) :=
  let A : Mat ℝ ((m + 1) + (m + 1)) (m + 1) := Fin.append C.step_basisᵀ (-C.step_basisᵀ)
  HPolytope.ofBounds (HPolytope.rowLin A) fun i => C.supportBound (HPolytope.rowLin A i)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `polytope(C, 'outer')`, branch by branch as `@capsule/polytope.m` takes them. -/
noncomputable def Capsule.hPolytope : {n : ℕ} → Capsule n → HPolytope (Vec ℝ n)
  | 0, C => if C.r < 0 then HPolytope.emptySet _ else HPolytope.ofPoint C.c
  | m + 1, C =>
    -- 1. an empty capsule: the empty polytope
    if C.r < 0 then HPolytope.emptySet _
    -- 2. `n = 1`: `aux_1D`, `[1; -1] x ≤ [c + |g| + r; -(c - |g| - r)]`
    else if m = 0 then C.interval.hPolytope
    -- 3. a point: `polytope(c)`
    else if C.g = 0 ∧ C.r = 0 then HPolytope.ofPoint C.c
    -- 4. a segment: `aux_exactLineConversion`
    else if C.r = 0 then C.hPolytopeOfLine
    -- 5. `'outer'`: `step_supportFunction`
    else C.hPolytopeOuter

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
