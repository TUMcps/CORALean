module

public import CORALean.ContSet.HPolytope.Real.Operations.OfBoundsOpt

@[expose] public section

/-!
# `HPolytope.ofBoundsOpt` encloses

The unanswered directions are exactly the ones that constrain nothing, so the
enclosure holds without any assumption about how many were answered.

## Inputs
* `Aq` – family indexed by `Fin q`

## Hypotheses
* `u` – an optional support bound of `S` along each row

## Conclusion
* `S` is contained in `ofBoundsOpt Aq u`
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ} {S : Set α}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.subset_ofBoundsOpt (Aq : Fin q → (α →ₗ[ℝ] ℝ))
    (u : ∀ i, Option (SupportBound S (Aq i))) : -- --- CONCL ---
    S ⊆ (HPolytope.ofBoundsOpt Aq u).construct := by -- --- PROOF ---
  intro x hx
  refine ⟨fun i => ?_, fun i => i.elim0⟩
  show ((u i).elim 0 fun _ => Aq i) x ≤ (u i).elim 0 SupportBound.val
  -- an unanswered direction leaves `0 x ≤ 0`, an answered one its own bound
  cases hu : u i with
  | none => exact le_rfl
  | some v => exact v.le x hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
