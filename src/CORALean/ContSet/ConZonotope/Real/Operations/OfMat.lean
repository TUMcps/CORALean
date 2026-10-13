module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.HPolytope.Real.Operations.Eqs

@[expose] public section

/-!
# `ConZonotope.ofMat`

CORA's `conZonotope(c, G, A, b)`, whose constraints are an equality system
`A β = b`. Here that system is one halfspace description among others, so the
constructor is `HPolytope.eqs` and nothing more.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.ofMat {q h : ℕ} (c : α) (G : Fin h → α) (A : Mat ℝ q h) (b : Vec ℝ q) :
    ConZonotope α :=
  ⟨h, c, G, HPolytope.eqs A b⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
