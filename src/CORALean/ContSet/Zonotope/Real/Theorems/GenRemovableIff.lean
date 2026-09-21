import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Data.Finset.Powerset

/-!
# [1, Prop. 2]: the generator-removal count

The `i`-th generator of the minuend spans one halfspace of [1, Thm. 2] for each
choice of the other `n - 2` of the `p_m - 1` remaining generators, and each of
those carries both signs: `2·C(p_m - 1, n - 2)` halfspaces in all. So the
printed sum `∑ⱼ ind⁽ʲ⁾ᵢ` over the *redundant* halfspaces reaches that number
exactly when every halfspace the generator spans is redundant, which is the
identification [1]'s own proof makes.

Which halfspaces are redundant is the parameter `Red`: the paper obtains it
by linear programming, and nothing here computes it. The step from "every
halfspace `i` spans is redundant" to "`i` is no longer required" is [1]'s
geometric assertion and is not proved here — it needs the minimum
H-representation to describe the difference. Ambient dimension `n + 2`, so a
facet's `n + 1` generators need no truncated subtraction.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2]: the printed count is reached exactly when every halfspace the
`i`-th generator spans is redundant. -/
theorem Zonotope.gen_removable_iff {n : ℕ} (Z : Zonotope (Vec ℝ (n + 2)))
    (Red : Finset (Bool × Finset (Fin Z.h))) (hRed : ∀ j ∈ Red, j.2.card = n + 1)
    (i : Fin Z.h) :
    ∑ j ∈ Red, (if i ∈ j.2 then 1 else 0) = 2 * (Z.h - 1).choose n
      ↔ ∀ (b : Bool) (S : Finset (Fin Z.h)),
          S.card = n + 1 → i ∈ S → (b, S) ∈ Red := by -- --- PROOF ---
  classical
  set B : Finset (Finset (Fin Z.h)) :=
    (Finset.univ.powersetCard (n + 1)).filter (fun S => i ∈ S) with hBdef
  set A : Finset (Bool × Finset (Fin Z.h)) := (Finset.univ : Finset Bool) ×ˢ B with hAdef
  have hB : B.card = (Z.h - 1).choose n := by
    have h := Finset.card_filter_powersetCard_subset {i} (Finset.univ : Finset (Fin Z.h))
      (n + 1) (Finset.subset_univ _) (by simp)
    rw [hBdef]
    simpa [Finset.singleton_subset_iff, Finset.card_univ] using h
  -- both signs of each such subset: the `2` of the printed count
  have hA : A.card = 2 * (Z.h - 1).choose n := by
    rw [hAdef, Finset.card_product, Finset.card_univ, Fintype.card_bool, hB]
  have hsum : ∑ j ∈ Red, (if i ∈ j.2 then 1 else 0)
      = (Red.filter (fun j => i ∈ j.2)).card := (Finset.card_filter _ _).symm
  have hsub : Red.filter (fun j => i ∈ j.2) ⊆ A := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [hAdef, Finset.mem_product, hBdef, Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨Finset.mem_univ _, ⟨Finset.subset_univ _, hRed j hj.1⟩, hj.2⟩
  -- the sum counts a subfamily of `A`, so it reaches `A.card` only by being all of it
  rw [hsum, ← hA]
  constructor
  · intro hcard b S hScard hiS
    have heq : Red.filter (fun j => i ∈ j.2) = A :=
      Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
    have : (b, S) ∈ Red.filter (fun j => i ∈ j.2) := by
      rw [heq, hAdef, Finset.mem_product, hBdef, Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨Finset.mem_univ _, ⟨Finset.subset_univ _, hScard⟩, hiS⟩
    exact (Finset.mem_filter.mp this).1
  · -- conversely, every halfspace `i` spans is then in `Red` and survives the filter
    intro hall
    refine le_antisymm (Finset.card_le_card hsub) ?_
    refine Finset.card_le_card fun j hj => ?_
    rw [hAdef, Finset.mem_product, hBdef, Finset.mem_filter, Finset.mem_powersetCard] at hj
    exact Finset.mem_filter.mpr ⟨hall j.1 j.2 hj.2.1.2 hj.2.2, hj.2.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
