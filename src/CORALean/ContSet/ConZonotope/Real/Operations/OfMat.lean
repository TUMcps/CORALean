import CORALean.ContSet.ConZonotope.Real.ConZonotope
import CORALean.ContSet.HPolytope.Real.Operations.OfMat

/-!
# `ConZonotope.ofMat`

CORA's `conZonotope(c, G, A, b)`, whose constraints are an equality system
`A β = b`. Here that system is one halfspace description among others, so the
constructor is `HPolytope.eqs` and nothing more.

`mem_ofMat_iff` reads the constraint back as the matrix equation, which is the
form a caller coming from CORA states it in; it is two lines and about this
constructor alone, so it stays beside it.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConZonotope.ofMat {q h : ℕ} (c : α) (G : Fin h → α) (A : Mat ℝ q h) (b : Vec ℝ q) :
    ConZonotope α :=
  ⟨h, c, G, HPolytope.eqs A b⟩

theorem ConZonotope.mem_ofMat_iff {q h : ℕ} {c : α} {G : Fin h → α} {A : Mat ℝ q h}
    {b : Vec ℝ q} {x : α} :
    x ∈ (ConZonotope.ofMat c G A b).construct ↔
      ∃ β : Fin h → ℝ, (∀ j, |β j| ≤ 1) ∧ (∀ i, (A *ᵥ β) i = b i)
        ∧ x = c + ∑ j, β j • G j :=
  ⟨fun ⟨β, hβ, hP, hx⟩ => ⟨β, hβ, HPolytope.mem_eqs_iff.mp hP, hx⟩,
   fun ⟨β, hβ, hA, hx⟩ => ⟨β, hβ, HPolytope.mem_eqs_iff.mpr hA, hx⟩⟩

end CORALean.Real
