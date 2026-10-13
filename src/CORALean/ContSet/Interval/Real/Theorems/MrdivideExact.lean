module

public import CORALean.ContSet.Interval.Real.Operations.Mrdivide
public import CORALean.ContSet.Interval.Real.Theorems.IsNonempty

@[expose] public section

/-!
# `Interval.mrdivide` is exactly the image under division by `d`

For `d ≠ 0` each coordinate's two quotients bracket the quotients of the points between, and
every value between them is reached. The sign of `d` decides which quotient is the lower one,
which is what `min` and `max` absorb.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mrdivide_exact {I : Interval (Vec ℝ n)} (hI : I.IsNonempty) {d : ℝ}
    (hd : d ≠ 0) :
    (I.mrdivide d).construct = (fun x i => x i / d) '' I.construct := by -- --- PROOF ---
  ext z
  constructor
  · intro hz
    refine ⟨fun i => z i * d, fun i => ?_, funext fun i => mul_div_cancel_right₀ _ hd⟩
    have h₁ : min (I.inf i / d) (I.sup i / d) ≤ z i := (hz i).1
    have h₂ : z i ≤ max (I.inf i / d) (I.sup i / d) := (hz i).2
    have hi : I.inf i ≤ I.sup i := hI i
    show I.inf i ≤ z i * d ∧ z i * d ≤ I.sup i
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · -- the sign flips the quotients: the supremum's is the lower
      rw [min_eq_right (div_le_div_of_nonpos_of_le hneg.le hi)] at h₁
      rw [max_eq_left (div_le_div_of_nonpos_of_le hneg.le hi)] at h₂
      exact ⟨(le_div_iff_of_neg hneg).mp h₂, (div_le_iff_of_neg hneg).mp h₁⟩
    · rw [min_eq_left (div_le_div_of_nonneg_right hi hpos.le)] at h₁
      rw [max_eq_right (div_le_div_of_nonneg_right hi hpos.le)] at h₂
      exact ⟨(div_le_iff₀ hpos).mp h₁ |> fun h => by linarith, (le_div_iff₀ hpos).mp h₂ |>
        fun h => by linarith⟩
  · rintro ⟨x, hx, rfl⟩ i
    have h₁ : I.inf i ≤ x i := (hx i).1
    have h₂ : x i ≤ I.sup i := (hx i).2
    show min (I.inf i / d) (I.sup i / d) ≤ x i / d ∧ x i / d ≤ max (I.inf i / d) (I.sup i / d)
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · exact ⟨(min_le_right _ _).trans (div_le_div_of_nonpos_of_le hneg.le h₂),
        (div_le_div_of_nonpos_of_le hneg.le h₁).trans (le_max_left _ _)⟩
    · exact ⟨(min_le_left _ _).trans (div_le_div_of_nonneg_right h₁ hpos.le),
        (div_le_div_of_nonneg_right h₂ hpos.le).trans (le_max_right _ _)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
