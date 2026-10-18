module

public import CORALean.ContDynamics.Conform.Definitions.TemplateZono
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Prod

@[expose] public section

/-!
# A sum of stretched templates over `Fin k`

`⨁_{i<k} ⟨cᵢ, Gᵢ diag(αᵢ)⟩ = ⟨∑ cᵢ, [G₀ ⋯ G_{k-1}] diag([α₀; ⋯; α_{k-1}])⟩`, the generators
indexed by `Fin k × ι`: one copy of the template per time step, as the disturbances of
a reachable set enter one per step.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

theorem Conform.sum_templateZono {m k : ℕ} {ι : Type} [Fintype ι] (c : Fin k → Vec ℝ m)
    (G : Fin k → ι → Vec ℝ m) (α : Fin k → ι → ℝ) : -- --- STMT ---
    ∑ i : Fin k, Conform.templateZono (c i) (G i) (α i)
      = Conform.templateZono (∑ i, c i) (fun r : Fin k × ι => G r.1 r.2)
          (fun r => α r.1 r.2) := by -- --- PROOF ---
  ext y
  rw [Set.mem_fintype_sum]
  constructor
  · rintro ⟨g, hg, rfl⟩
    choose β hβ hgβ using hg
    refine ⟨fun r => β r.1 r.2, fun r => hβ r.1 r.2, ?_⟩
    simp only [hgβ, Finset.sum_add_distrib, Fintype.sum_prod_type]
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨fun i => c i + ∑ j, β (i, j) • α i j • G i j,
      fun i => ⟨fun j => β (i, j), fun j => hβ _, rfl⟩, ?_⟩
    simp only [Finset.sum_add_distrib, Fintype.sum_prod_type]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
