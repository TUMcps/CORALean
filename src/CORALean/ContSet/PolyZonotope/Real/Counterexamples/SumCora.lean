module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Sum
public import CORALean.ContSet.PolyZonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SumPoint
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `PolyZonotope.sumCora`: `sum` as CORA's code computes it

`@polyZonotope/sum.m` accumulates the centre in a loop over the list, and the body reads
`c = c + pZlist{1}.c` where it means `pZlist{i}.c`: the first summand's centre is added once
per summand, and no other. Everything else is `sum`; only the centre differs, and it is wrong
as soon as the list has two entries that differ (`sum_cora_counterexample`). Read from the
source, not run.

# CORA's `polyZonotope/sum` has the wrong centre

For `pZ = {0}` and the list `{1}, {2}` (all three are points) the Minkowski sum is `{3}`, and
`sum` returns it. CORA's loop adds `pZlist{1}.c` twice and returns `{0 + 1 + 1} = {2}`.
Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- The model: CORA's code as printed, kept only to be refuted.
/-- `sum` with CORA's centre: `pZ.c` plus `(L 0).c` once for each summand. -/
def PolyZonotope.sumCora {m : ℕ} (pZ : PolyZonotope α) (L : Fin m → PolyZonotope α)
    (hp : ∀ i, (L i).p = pZ.p) : PolyZonotope α :=
  { pZ.sum L hp with
    c := pZ.c + if h : 0 < m then ∑ _i : Fin m, (L ⟨0, h⟩).c else 0 }

end CORALean.Real

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- With no generators of either kind the set is its centre. -/
theorem PolyZonotope.aux_mem_of_noGens (Z : PolyZonotope ℝ) (hh : Z.h = 0) (hq : Z.q = 0)
    (x : ℝ) : x ∈ Z.construct ↔ x = Z.c := by -- --- PROOF ---
  haveI : IsEmpty (Fin Z.h) := by rw [hh]; infer_instance
  haveI : IsEmpty (Fin Z.q) := by rw [hq]; infer_instance
  constructor
  · rintro ⟨a, β, -, -, hx⟩
    simpa using hx
  · rintro rfl
    exact ⟨fun _ => 0, fun j => (IsEmpty.false j).elim, fun k => by simp,
      fun j => (IsEmpty.false j).elim, by simp⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's centre is not the sum's, and the sets differ: `{2}` against `{3}`. -/
theorem PolyZonotope.sum_cora_counterexample :
    ∃ (pZ : PolyZonotope ℝ) (L : Fin 2 → PolyZonotope ℝ) (hp : ∀ i, (L i).p = pZ.p),
      (pZ.sumCora L hp).construct ≠ (pZ.sum L hp).construct := by -- --- PROOF ---
  refine ⟨.ofPoint 0, ![.ofPoint 1, .ofPoint 2], fun i => by fin_cases i <;> rfl, fun h => ?_⟩
  -- both sums are the point at their own centre, `2` against `3`
  have h2 : (2 : ℝ) ∈ (PolyZonotope.sumCora (.ofPoint 0) ![.ofPoint 1, .ofPoint 2]
      fun i => by fin_cases i <;> rfl).construct :=
    (PolyZonotope.aux_mem_of_noGens _
      (by simp [PolyZonotope.sumCora, PolyZonotope.sum, PolyZonotope.ofPoint])
      (by simp [PolyZonotope.sumCora, PolyZonotope.sum, PolyZonotope.ofPoint]) _).mpr
      (by simp [PolyZonotope.sumCora, PolyZonotope.sum, PolyZonotope.ofPoint])
  rw [h] at h2
  have := (PolyZonotope.aux_mem_of_noGens _ (by simp [PolyZonotope.sum, PolyZonotope.ofPoint])
      (by simp [PolyZonotope.sum, PolyZonotope.ofPoint]) _).mp h2
  simp [PolyZonotope.sum, PolyZonotope.ofPoint] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
