module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ExtPolyZonotope
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemExtPolyZonotopeIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# `ConPolyZono.containsPointCora`

What CORA's source passes for a numeric operand: `S = [S; ones(m, size(S,2))]`, the extended point
`[p; 1]`, where the construction needs `[p; 0]` (`ConPolyZono.containsPoint`). Run in MATLAB R2024b
with CORA v2026.1.0 (904a444), see `experiments/cora-bugs/results.tsv`, on another instance: CORA's
`'approx'` point test decides a point only inside a full-dimensional extended set, and the extended
set of the instance below is a curve, where MATLAB answers `0` even for the member `0`. The set `x =
α₁ + α₂` with the constraint `α₂ = -1/2`, which is `[-3/2, 1/2]`, has a full-dimensional extended
set: CORA accepts `p = 1` and rejects the members `-1` and `-1/2`.

# CORA's `conPolyZono/contains_` extends a numeric operand by ones

The constraint `α = 0` on the single factor of `{α : |α| ≤ 1}` leaves the set `{0}`. CORA's numeric
branch tests `[p; 1]` in the extended polynomial zonotope, whose last coordinate is `α - 0`: the
point `p = 1`, reached at `α = 1`, passes, though `1` is not in the set.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA accepts a point outside the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- `[p; ones(m)]` lies in the extended polynomial zonotope. -/
def ConPolyZono.containsPointCora (cPZ : ConPolyZono (Vec ℝ n)) (p : Vec ℝ n) : Prop :=
  (p, fun _ => 1) ∈ cPZ.extPolyZonotope.construct

end CORALean.Real

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.containsPointCora_counterexample : -- --- CONCL ---
    ∃ (cPZ : ConPolyZono (Vec ℝ 1)) (p : Vec ℝ 1),
      cPZ.containsPointCora p ∧ p ∉ cPZ.construct := by -- --- PROOF ---
  -- one factor `α`, generator `α`, constraint `α = 0`
  let cPZ : ConPolyZono (Vec ℝ 1) :=
    ⟨1, 1, 0, fun _ => 0, fun _ _ => 1, fun _ _ => 1, Fin.elim0, ⟨1, 1, Matrix.of fun _ _ => 1,
        fun _ _ => 1, fun _ => 0, fun _ => .eq, Interval.unit 1⟩,
      fun _ => rfl, rfl⟩
  refine ⟨cPZ, fun _ => 1, ?_, ?_⟩
  · -- `α = 1` passes the extended test
    unfold ConPolyZono.containsPointCora
    rw [ConPolyZono.mem_extPolyZonotope_iff]
    refine ⟨fun _ => 1, Fin.elim0, fun _ => by simp, fun j => j.elim0, fun i => ?_, ?_⟩
    · simp [cPZ, Matrix.mulVec, dotProduct, PolyZonotope.monomial]
    · funext i
      simp [cPZ, PolyZonotope.monomial]
  · -- but the constraint pins `α = 0`, so `1` is not in the set
    rintro ⟨a, β, hβ, hs, hx⟩
    have h0 := ((PolyLevelSet.mem_construct_iff_of_eq cPZ.cons_eq).mp hs).2 0
    simp [cPZ, Matrix.mulVec, dotProduct, PolyZonotope.monomial] at h0
    have h1 := congrFun hx 0
    simp [cPZ, PolyZonotope.monomial] at h1
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
