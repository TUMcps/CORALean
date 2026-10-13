import CORALean.ContSet.Interval.Real.Operations.Cos
import CORALean.ContSet.Interval.Real.Theorems.ImageCosIcc

/-!
# `Interval.cos` is exactly the image under `Real.cos`

Coordinate by coordinate, `Interval.image_cos_Icc`. A crossed coordinate (`ub < lb`) would give
a nonempty box for an empty one, so the statement is for a nonempty box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.cos_exact (I : Interval (Vec ℝ n)) (hI : ∀ i, I.inf i ≤ I.sup i) :
    I.cos.construct = (fun x i => Real.cos (x i)) '' I.construct := by -- --- PROOF ---
  ext y
  constructor
  · intro hy
    have hex : ∀ i, ∃ x, x ∈ Set.Icc (I.inf i) (I.sup i) ∧ Real.cos x = y i := fun i => by
      have h := (Interval.image_cos_Icc (hI i)).symm.subset (hy i)
      exact h
    choose x hx hfx using hex
    exact ⟨x, fun i => hx i, funext hfx⟩
  · rintro ⟨x, hx, rfl⟩ i
    exact (Interval.image_cos_Icc (hI i)).subset ⟨x i, hx i, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
