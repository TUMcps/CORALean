module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq
public import CORALean.Global.StepOf

@[expose] public section

/-!
# CORA's `representsa_(cPZ, 'emptySet')` answers "not empty" before reading the constraints

CORA's `@conPolyZono/representsa_.m`, `aux_isEmptySet`, begins with
`if ~isempty(cPZ.GI): res = false; return`, that is, "not empty" as soon as the independent
generators are nonempty, before the constraints are looked at. A constrained polynomial zonotope
is empty whenever its constraints have no solution in the box, whatever `GI` is.

The example has one factor, no dependent generators, one independent generator `GI = 1` and the
constraint `α₁ = 2`, which no `α₁ ∈ [-1, 1]` satisfies. `ConPolyZono.construct` is `∅`, and the
printed check answers `false`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA answers not empty for an empty set
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The part of `aux_isEmptySet` that precedes the contractor: `some false` ("not empty") when
`GI` is nonempty, `none` for the rest (the constraint check and the contraction of the domain,
which are not modelled). -/
@[step_of ConPolyZono.representsa_empty_counterexample]
def ConPolyZono.step_isEmptySetPrinted {α : Type} (cPZ : ConPolyZono α) : Option Bool :=
  let giNonempty := decide (0 < cPZ.qI)
  if giNonempty then some false else none

/-- One factor, `c = 0`, `GI = 1`, and the constraint `1 · α₁ = 2`. -/
@[step_of ConPolyZono.representsa_empty_counterexample]
def ConPolyZono.step_emptyWithGI : ConPolyZono ℝ :=
  ⟨1, 0, 1, 0, Fin.elim0, fun _ _ => 0, fun _ => 1, ⟨1, 1, fun _ _ => 1, fun _ _ => 1, fun _ => 2,
      fun _ => .eq, Interval.unit 1⟩,
      fun _ => rfl, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set is empty although `GI` is nonempty, and CORA's printed check answers "not empty". -/
theorem ConPolyZono.representsa_empty_counterexample : -- --- CONCL ---
    0 < ConPolyZono.step_emptyWithGI.qI ∧ ConPolyZono.step_emptyWithGI.construct = ∅ ∧
      ConPolyZono.step_isEmptySetPrinted ConPolyZono.step_emptyWithGI
        = some false := by -- --- PROOF ---
  refine ⟨Nat.one_pos, ?_,
    by simp [ConPolyZono.step_isEmptySetPrinted, ConPolyZono.step_emptyWithGI]⟩
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, β, -, hs, -⟩
  have h4 :=
    ((PolyLevelSet.mem_construct_iff_of_eq ConPolyZono.step_emptyWithGI.cons_eq).mp hs).2
      (0 : Fin 1)
  have h3 := (Interval.mem_unit_iff a).mp hs.1 (0 : Fin 1)
  simp [ConPolyZono.step_emptyWithGI, PolyZonotope.monomial, Matrix.mulVec, dotProduct] at h4 h3
  rw [h4] at h3
  norm_num [abs_of_pos] at h3

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
