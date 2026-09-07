import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope

/-!
# The tightest of a bundle's component bounds

The intersection sits inside every component, so any component's
`Zonotope.supportBound` bounds it too, `SupportBound.mono` at
`Set.iInter_subset`; the least of them is the tightest such bound available
this way. Needs the index nonempty, which is exactly
`ZonoBundle.isCompact_construct`'s hypothesis and for the same reason: at
`k = 0` the bundle is the whole space, unbounded in every nonzero direction.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One component's bound, read back as a bound on the whole bundle — the
result type is what pins the metavariables `SupportBound.mono` would
otherwise leave to the caller. -/
def aux_componentBound (B : ZonoBundle α) (c : α →ₗ[ℝ] ℝ) (i : Fin B.k) :
    SupportBound B.construct c :=
  SupportBound.mono (Set.iInter_subset (fun i => (B.Z i).construct) i) ((B.Z i).supportBound c)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The minimum over the family's own component bounds, proved tight against
the component that attains it. -/
noncomputable def ZonoBundle.supportBound (B : ZonoBundle α) (hk : 0 < B.k)
    (c : α →ₗ[ℝ] ℝ) : SupportBound B.construct c where
  val := Finset.univ.inf' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ (fun i => (aux_componentBound B c i).val)
  le := by
    intro x hx
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Fin B.k)))
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩ (fun i => (aux_componentBound B c i).val)
    rw [hi]
    exact (aux_componentBound B c i).le x hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
