module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.ImageCosIcc

@[expose] public section

/-!
# `Interval.sin` is exactly the image under `Real.sin`

`sin x = cos (x - π/2)`, so the image of `[lb, ub]` under the sine is that of
`[lb - π/2, ub - π/2]` under the cosine, `Interval.image_cos_Icc`. For a nonempty box, as for
`Interval.cos_exact`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One coordinate: the sine image of `[lb, ub]` is the cosine image of the shifted range. -/
theorem aux_image_sin_Icc (lb ub : ℝ) :
    Real.sin '' Set.Icc lb ub =
      Real.cos '' Set.Icc (lb - Real.pi / 2) (ub - Real.pi / 2) := by -- --- PROOF ---
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x - Real.pi / 2, ⟨by linarith [hx.1], by linarith [hx.2]⟩, Real.cos_sub_pi_div_two x⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x + Real.pi / 2, ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
    rw [← Real.cos_sub_pi_div_two, add_sub_cancel_right]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.sin_exact (I : Interval (Vec ℝ n)) (hI : ∀ i, I.inf i ≤ I.sup i) :
    I.sin.construct = (fun x i => Real.sin (x i)) '' I.construct := by -- --- PROOF ---
  have hJ : ∀ i, I.inf i - Real.pi / 2 ≤ I.sup i - Real.pi / 2 := fun i => by linarith [hI i]
  have hc : ∀ i, Real.sin '' Set.Icc (I.inf i) (I.sup i) = Set.Icc
      (-Interval.maxCos (I.inf i - Real.pi / 2 - Real.pi) (I.sup i - Real.pi / 2 - Real.pi))
      (Interval.maxCos (I.inf i - Real.pi / 2) (I.sup i - Real.pi / 2)) := fun i => by
    rw [aux_image_sin_Icc, Interval.image_cos_Icc (hJ i)]
  ext y
  constructor
  · intro hy
    have hex : ∀ i, ∃ x, x ∈ Set.Icc (I.inf i) (I.sup i) ∧ Real.sin x = y i := fun i => by
      have h := (hc i).symm.subset (hy i)
      exact h
    choose x hx hfx using hex
    exact ⟨x, fun i => hx i, funext hfx⟩
  · rintro ⟨x, hx, rfl⟩ i
    exact (hc i).subset ⟨x i, hx i, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
