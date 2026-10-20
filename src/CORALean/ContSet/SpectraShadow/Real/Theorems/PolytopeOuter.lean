module

public import CORALean.ContSet.SpectraShadow.Real.Operations.PolytopeOuter
public import CORALean.ContSet.SpectraShadow.Real.Theorems.TranslateMem
public import CORALean.ContSet.SpectraShadow.Real.Theorems.Basic

@[expose] public section

/-!
# The outer polytope of a shadow encloses it

Every point of the shadow satisfies each kept row: `dᵀ(x - c) ≤ supportFunc (SpS - c) d` since
the support function is a supremum, and the value is finite for a kept row, so the inequality
holds in `ℝ`; shifted back by `c` it is `dᵀ x ≤ val + dᵀ c`. Whatever `c` is. Outer: a
polytope with finitely many rows is not the shadow.

## Inputs
* `S` – spectrahedral shadow
* `c` – center of length `n`
* `dirs` – family indexed by `Fin N`

## Hypotheses
* none

## Conclusion
* the outer polytope of a shadow encloses it
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Classical

variable {n N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_polytopeOuter_row (S : SpectraShadow (Vec ℝ n)) (c : Vec ℝ n)
    (dirs : Fin N → (Vec ℝ n →ₗ[ℝ] ℝ)) {x : Vec ℝ n} (hx : x ∈ S.construct) (i : Fin N)
    (hi : (S.translate (-c)).supportFunc (dirs i) ≠ ⊤ ∧
      (S.translate (-c)).supportFunc (dirs i) ≠ ⊥) : -- --- CONCL ---
    dirs i x ≤ ((S.translate (-c)).supportFunc (dirs i)).toReal + dirs i c := by -- --- PROOF ---
  have hmem : x - c ∈ (S.translate (-c)).construct := by
    rw [SpectraShadow.mem_translate_iff]
    simpa using hx
  have hle := (S.translate (-c)).le_supportFunc_of_mem (dirs i) hmem
  have hval : (((S.translate (-c)).supportFunc (dirs i)).toReal : EReal)
      = (S.translate (-c)).supportFunc (dirs i) := EReal.coe_toReal hi.1 hi.2
  rw [← hval, EReal.coe_le_coe_iff, map_sub] at hle
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.polytopeOuter_outer (S : SpectraShadow (Vec ℝ n)) (c : Vec ℝ n)
    (dirs : Fin N → (Vec ℝ n →ₗ[ℝ] ℝ)) : -- --- CONCL ---
    S.construct ⊆ (S.polytopeOuter c dirs).construct := by -- --- PROOF ---
  intro x hx
  have hne : S.construct ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨x, hx⟩
  unfold SpectraShadow.polytopeOuter
  rw [if_neg hne]
  refine ⟨fun r => ?_, fun r => Fin.elim0 r⟩
  exact aux_polytopeOuter_row S c dirs hx _
    (by simpa using (List.mem_filter.1 (List.get_mem _ r)).2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
