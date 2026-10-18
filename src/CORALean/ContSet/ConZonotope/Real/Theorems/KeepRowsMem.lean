module

public import CORALean.ContSet.ConZonotope.Real.Operations.KeepRows

@[expose] public section

/-!
# `keepRows` admits what the dropped coordinates leave behind

A coefficient vector in `P` whose dropped coordinates lie in `[-1, 1]` has its kept
coordinates in `keepRows`. A row `f` splits along the partition into the kept part,
which is `f` at `keepEmbed`, and a dropped part `∑ₗ β_{right l} · f e_{right l}`
bounded by `keepSlack`; the row's own bound then holds up to that slack.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {h q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A row splits along a partition: kept coordinates through `keepEmbed`, dropped ones
as a weighted sum. -/
theorem ConZonotope.aux_apply_split (part : Split (Fin h) into (Fin q) ⊕ (Fin r))
    (f : Vec ℝ h →ₗ[ℝ] ℝ) (β : Vec ℝ h) : -- --- STMT ---
    f β = f (ConZonotope.keepEmbed part (fun l => β (part.left l)))
      + ∑ l, β (part.right l)
        * f (Pi.single (part.right l) (1 : ℝ) : Vec ℝ h) := by -- --- PROOF ---
  -- a vector is the sum of its coordinates times the unit vectors
  have hβ : β = ∑ j, β j • (Pi.single j (1 : ℝ) : Vec ℝ h) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hf : f β = ∑ j, β j * f (Pi.single j (1 : ℝ) : Vec ℝ h) := by
    conv_lhs => rw [hβ]
    simp [map_sum]
  rw [hf, part.sum_split₂ fun j => β j * f (Pi.single j (1 : ℝ) : Vec ℝ h)]
  simp [ConZonotope.keepEmbed, map_sum]

/-- The dropped part of a row is bounded by its slack when the coordinates are. -/
theorem ConZonotope.aux_abs_dropped_le (part : Split (Fin h) into (Fin q) ⊕ (Fin r))
    (f : Vec ℝ h →ₗ[ℝ] ℝ) {β : Vec ℝ h} (hbox : ∀ l, |β (part.right l)| ≤ 1) :
    |∑ l, β (part.right l) * f (Pi.single (part.right l) (1 : ℝ) : Vec ℝ h)|
      ≤ ConZonotope.keepSlack part f := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_right (hbox l) (abs_nonneg _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.keepRows_mem (P : HPolytope (Vec ℝ h))
    (part : Split (Fin h) into (Fin q) ⊕ (Fin r)) {β : Vec ℝ h} (hβ : β ∈ P.construct)
    (hbox : ∀ l, |β (part.right l)| ≤ 1) :
    (fun l => β (part.left l)) ∈ (ConZonotope.keepRows P part).construct := by -- --- PROOF ---
  obtain ⟨hA, hAe⟩ := hβ
  refine ⟨?_, fun i => i.elim0⟩
  -- the rows come in three blocks: inequalities, equalities as `≤`, equalities as `≥`
  refine Fin.addCases (fun i => ?_) (fun i => ?_)
  · simp only [ConZonotope.keepRows, Fin.append_left, LinearMap.comp_apply]
    have h1 := ConZonotope.aux_apply_split part (P.A i) β
    have h2 := (abs_le.mp (ConZonotope.aux_abs_dropped_le part (P.A i) hbox)).1
    linarith [hA i]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [ConZonotope.keepRows, Fin.append_left, Fin.append_right, LinearMap.comp_apply]
      have h1 := ConZonotope.aux_apply_split part (P.Ae i) β
      have h2 := (abs_le.mp (ConZonotope.aux_abs_dropped_le part (P.Ae i) hbox)).1
      linarith [hAe i]
    · simp only [ConZonotope.keepRows, Fin.append_right, LinearMap.comp_apply,
        LinearMap.neg_apply]
      have h1 := ConZonotope.aux_apply_split part (P.Ae i) β
      have h2 := (abs_le.mp (ConZonotope.aux_abs_dropped_le part (P.Ae i) hbox)).2
      linarith [hAe i]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
