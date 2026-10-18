module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# The tightest of a bundle's component bounds

The intersection sits inside every component, so any component's
`Zonotope.supportBound` bounds it too, `SupportBound.mono` at
`Set.iInter_subset`; the least of them is the tightest such bound available
this way. Needs the index nonempty, which is exactly
`SetIntersection.isCompact_construct`'s hypothesis and for the same reason: at
`k = 0` the bundle is the whole space, unbounded in every nonzero direction.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One component's bound, read back as a bound on the whole bundle — the
result type is what pins the metavariables `SupportBound.mono` would
otherwise leave to the caller. -/
def aux_componentBound (zB : ZonoBundle α) (c : α →ₗ[ℝ] ℝ) (i : Fin zB.k) :
    SupportBound zB.construct c :=
  SupportBound.mono (SetIntersection.construct_subset_ofFn _ i)
    ((zB.Z i).supportBound c)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The minimum over the family's own component bounds, proved tight against
the component that attains it. -/
noncomputable def ZonoBundle.supportBound (zB : ZonoBundle α) (hk : 0 < zB.k)
    (c : α →ₗ[ℝ] ℝ) : SupportBound zB.construct c where
  val := Finset.univ.inf' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ (fun i => (aux_componentBound zB c i).val)
  le := by
    intro x hx
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Fin zB.k)))
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩ (fun i => (aux_componentBound zB c i).val)
    rw [hi]
    exact (aux_componentBound zB c i).le x hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
