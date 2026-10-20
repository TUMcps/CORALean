module

public import CORALean.ContSet.HPolytope.Float.Operations.ContractBox
public import CORALean.ContSet.HPolytope.Float.Theorems.RowsOfMemConstruct
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.ContractHalfspaceOuter

@[expose] public section

/-!
# `HPolytope.contractBox` holds the box's intersection with the polytope

A point of both satisfies every row the fold cuts with, an equality row's two
halves included, and `Interval.contractHalfspace_outer` keeps it at each.

## Inputs
* `P` – H-polytope
* `I` – interval

## Hypotheses
* none

## Conclusion
* `HPolytope.contractBox` holds the box's intersection with the polytope
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point every row holds at stays in the box through the whole fold. -/
theorem aux_mem_foldl_contractHalfspace {x : Vec ℝ n} :
    ∀ (rows : List (Vec 𝕋 n × 𝕋)), (∀ r ∈ rows, ∑ j, toReal (r.1 j) * x j ≤ toReal r.2) →
      ∀ J : Interval (Vec 𝕋 n), x ∈ J.construct →
        x ∈ (rows.foldl (fun J r => (J.contractHalfspace r.1 r.2).materialise) J).construct
  | [], _, _, hJ => hJ
  | r :: rows, hrows, J, hJ => by
    rw [List.foldl_cons]
    refine aux_mem_foldl_contractHalfspace rows
      (fun r' hr' => hrows r' (List.mem_cons_of_mem _ hr')) _ ?_
    rw [Interval.materialise_eq]
    exact J.contractHalfspace_outer r.1 r.2 hJ (hrows r List.mem_cons_self)


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.contractBox_outer (P : HPolytope 𝕋 (Vec 𝕋 n))
    (I : Interval (Vec 𝕋 n)) : -- --- CONCL ---
    I.construct ∩ P.construct ⊆ (P.contractBox I).construct := by -- --- PROOF ---
  rintro x ⟨hI, hP⟩
  obtain ⟨hle, heq⟩ := HPolytope.rows_of_mem_construct hP
  -- each row of `P`, read as the sum the contraction asks for, is one `hle`/`heq` gives
  refine aux_mem_foldl_contractHalfspace _ (fun r hr => ?_) I hI
  simp only [List.mem_append, List.mem_map, List.mem_finRange, true_and] at hr
  rcases hr with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · exact hle i
  · exact (heq i).1
  · -- the lower half of an equality row, negated into an upper one
    have h := (heq i).2
    simp only [Pi.neg_apply, toReal_neg', neg_mul, Finset.sum_neg_distrib]
    exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
