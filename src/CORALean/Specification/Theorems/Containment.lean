import CORALean.Specification.Specification
import CORALean.ContSet.HPolytope.Real.Theorems.MemConstruct
import CORALean.Global.LinProg.LinProg

/-!
# Bounds certify that a safe set is stayed inside

A safe set given by halfspaces is checked one halfspace at a time, and each is a
bound in that halfspace's own direction — the same object `Global.LinProg`
returns, so nothing new is needed to discharge the check.

An equality row costs two bounds rather than one, its direction having to be
answered from both sides; that is what makes it the expensive kind of
constraint to verify against, not the expensive kind to state.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O : Set α}

/-- A safe set cut out by directions, checked in each of them. -/
theorem subset_halfspaces {ι : Type} (c : ι → α →ₗ[ℝ] ℝ) (d : ι → ℝ)
    (u : ∀ i, SupportBound O (c i)) (h : ∀ i, (u i).val ≤ d i) :
    O ⊆ {x | ∀ i, c i x ≤ d i} :=
  fun _ hx i => le_trans ((u i).le _ hx) (h i)

/-- The same at a halfspace description, where an equality row is the two
inequalities it stands for. -/
theorem subset_hPolytope (P : HPolytope α)
    (u : ∀ i, SupportBound O (P.A i)) (hu : ∀ i, (u i).val ≤ P.b i)
    (e : ∀ i, SupportBound O (P.Ae i)) (he : ∀ i, (e i).val ≤ P.be i)
    (f : ∀ i, SupportBound O (-P.Ae i)) (hf : ∀ i, (f i).val ≤ -P.be i) :
    O ⊆ P.construct := by
  intro x hx
  refine HPolytope.mem_construct_iff.mpr ⟨fun i => le_trans ((u i).le x hx) (hu i), fun i => ?_⟩
  have hle : P.Ae i x ≤ P.be i := le_trans ((e i).le x hx) (he i)
  have hge := (f i).le x hx
  rw [LinearMap.neg_apply] at hge
  linarith [hf i]

theorem Specification.holds_safeSet_of_bounds {ι : Type} (c : ι → α →ₗ[ℝ] ℝ) (d : ι → ℝ)
    (u : ∀ i, SupportBound O (c i)) (h : ∀ i, (u i).val ≤ d i) :
    (Specification.safeSet {x | ∀ i, c i x ≤ d i}).Holds O :=
  subset_halfspaces c d u h

end CORALean.Real
