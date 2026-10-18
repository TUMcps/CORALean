module

public import CORALean.ContSet.HPolytope.Real.Theorems.MemConstruct
public import CORALean.Global.SupportFunction.SupportFunction
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Bounds certify containment in a halfspace description

The same check as `subset_halfspaces`, at a bundled `HPolytope` rather than a
bare family of directions. An equality row costs two bounds rather than one,
its direction having to be answered from both sides; that is what makes it the
expensive kind of constraint to verify against, not the expensive kind to
state.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O : Set α}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same at a halfspace description, where an equality row is the two
inequalities it stands for. -/
theorem subset_hPolytope (P : HPolytope α)
    (u : ∀ i, SupportBound O (P.A i)) (hu : ∀ i, (u i).val ≤ P.b i)
    (e : ∀ i, SupportBound O (P.Ae i)) (he : ∀ i, (e i).val ≤ P.be i)
    (f : ∀ i, SupportBound O (-P.Ae i)) (hf : ∀ i, (f i).val ≤ -P.be i) : -- --- STMT ---
    O ⊆ P.construct := by -- --- PROOF ---
  intro x hx
  refine HPolytope.mem_construct_iff.mpr ⟨fun i => le_trans ((u i).le x hx) (hu i), fun i => ?_⟩
  have hle : P.Ae i x ≤ P.be i := le_trans ((e i).le x hx) (he i)
  have hge := (f i).le x hx
  rw [LinearMap.neg_apply] at hge
  linarith [hf i]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
