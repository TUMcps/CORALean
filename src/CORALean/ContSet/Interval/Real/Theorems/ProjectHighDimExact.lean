module

public import CORALean.ContSet.Interval.Real.Operations.ProjectHighDim
public import CORALean.ContSet.Interval.Real.Theorems.EmptyExact

@[expose] public section

/-!
# `Interval.projectHighDim_` is exactly the zero-padded set

The padding is `Function.extend proj · 0`. For distinct `proj`, a point of the padded box is `0`
off the range and bounded on it, so it is the padding of its own restriction. An empty box gives
`empty N`, which is empty because `proj` of a crossed coordinate makes `0 < N`.

## Inputs
* `I` – interval box
* `proj` – coordinate embedding

## Hypotheses
* `hproj` – embedding injective

## Conclusion
* the lifted box is exactly the zero-padded set
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {m N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.projectHighDim_exact (I : Interval (Vec ℝ m)) (proj : Fin m → Fin N)
    (hproj : Function.Injective proj) : -- --- CONCL ---
    (I.projectHighDim_ N proj).construct =
      (fun x => Function.extend proj x 0) '' I.construct := by -- --- PROOF ---
  by_cases hI : I.IsNonempty
  -- a nonempty box pads coordinate by coordinate
  · have hne : ¬I.representsa_emptySet := fun h => h hI
    rw [Interval.projectHighDim_, if_neg hne]
    refine Set.Subset.antisymm (fun z hz => ?_) ?_
    · refine ⟨fun k => z (proj k), fun k => ?_, funext fun j => ?_⟩
      · have h : Function.extend proj I.inf 0 (proj k) ≤ z (proj k) ∧
            z (proj k) ≤ Function.extend proj I.sup 0 (proj k) := hz (proj k)
        rw [hproj.extend_apply, hproj.extend_apply] at h
        exact h
      · by_cases h : ∃ k, proj k = j
        · obtain ⟨k, rfl⟩ := h
          exact hproj.extend_apply _ _ _
        · have h2 : Function.extend proj I.inf 0 j ≤ z j ∧ z j ≤ Function.extend proj I.sup 0 j :=
            hz j
          rw [Function.extend_apply' I.inf (0 : Fin N → ℝ) j h,
            Function.extend_apply' I.sup (0 : Fin N → ℝ) j h] at h2
          show Function.extend proj (fun k => z (proj k)) 0 j = z j
          rw [Function.extend_apply' (fun k => z (proj k)) (0 : Fin N → ℝ) j h]
          exact (le_antisymm h2.2 h2.1).symm
    · -- every padded member lies in the padded box
      rintro _ ⟨x, hx, rfl⟩ j
      by_cases h : ∃ k, proj k = j
      · obtain ⟨k, rfl⟩ := h
        show Function.extend proj I.inf 0 (proj k) ≤ Function.extend proj x 0 (proj k) ∧
          Function.extend proj x 0 (proj k) ≤ Function.extend proj I.sup 0 (proj k)
        rw [hproj.extend_apply, hproj.extend_apply, hproj.extend_apply]
        exact hx k
      · show Function.extend proj I.inf 0 j ≤ Function.extend proj x 0 j ∧
          Function.extend proj x 0 j ≤ Function.extend proj I.sup 0 j
        rw [Function.extend_apply' I.inf (0 : Fin N → ℝ) j h,
          Function.extend_apply' x (0 : Fin N → ℝ) j h,
          Function.extend_apply' I.sup (0 : Fin N → ℝ) j h]
        exact ⟨le_refl _, le_refl _⟩
  -- a crossed box gives `empty N`, and has no members
  · have hemp : I.representsa_emptySet := hI
    have hI' : I.construct = ∅ := (Interval.not_isNonempty_iff I).1 hI
    rw [Interval.projectHighDim_, if_pos hemp, hI', Set.image_empty]
    obtain ⟨i, _⟩ := not_forall.1 hI
    exact Interval.empty_exact (Nat.pos_of_ne_zero fun h => by subst h; exact (proj i).elim0)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
