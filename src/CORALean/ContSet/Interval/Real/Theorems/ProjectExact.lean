import CORALean.ContSet.Interval.Real.Theorems.ProjectOuter
import CORALean.ContSet.Interval.Real.Theorems.IsNonempty

/-!
# `Interval.project` is exactly the projected set

For a nonempty box and distinct coordinates: the coordinates not chosen are filled with `inf`,
which is in range as the box is nonempty. With a repeated coordinate the box can be strictly
larger than the image, so `Function.Injective dims` is needed.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.project_exact (I : Interval (Vec ℝ n)) (dims : Fin m → Fin n)
    (hdims : Function.Injective dims) (hI : I.IsNonempty) :
    (I.project dims).construct = (fun x k => x (dims k)) '' I.construct := by -- --- PROOF ---
  refine Set.Subset.antisymm (fun y hy => ?_) (Interval.project_outer I dims)
  refine ⟨Function.extend dims y I.inf, fun j => ?_, funext fun k => hdims.extend_apply _ _ _⟩
  by_cases h : ∃ k, dims k = j
  · obtain ⟨k, rfl⟩ := h
    show I.inf (dims k) ≤ Function.extend dims y I.inf (dims k) ∧
      Function.extend dims y I.inf (dims k) ≤ I.sup (dims k)
    rw [hdims.extend_apply]
    exact hy k
  · show I.inf j ≤ Function.extend dims y I.inf j ∧ Function.extend dims y I.inf j ≤ I.sup j
    rw [Function.extend_apply' _ _ _ h]
    exact ⟨le_refl _, hI j⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
