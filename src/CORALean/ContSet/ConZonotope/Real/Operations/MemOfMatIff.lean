module

public import CORALean.ContSet.ConZonotope.Real.Operations.OfMat
public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# Membership in `ConZonotope.ofMat`

Reads the constraint back as the matrix equation, which is the form a caller
coming from CORA states it in.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.mem_ofMat_iff {q h : ℕ} {c : α} {G : Fin h → α} {A : Mat ℝ q h}
    {b : Vec ℝ q} {x : α} :
    x ∈ (ConZonotope.ofMat c G A b).construct ↔
      ∃ β : Fin h → ℝ, (∀ j, |β j| ≤ 1) ∧ (∀ i, (A *ᵥ β) i = b i)
        ∧ x = c + ∑ j, β j • G j :=
  ⟨fun ⟨β, hβ, hP, hx⟩ => ⟨β, hβ, HPolytope.mem_eqs_iff.mp hP, hx⟩,
   fun ⟨β, hβ, hA, hx⟩ => ⟨β, hβ, HPolytope.mem_eqs_iff.mpr hA, hx⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
