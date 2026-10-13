module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Isequal

@[expose] public section

/-!
# Ellipsoids passing `isequal` denote the same set

Sound, not exact: `isequal` compares the generator matrices, and different `G` with the same
`G Gᵀ` denote the same ellipsoid.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isequal_construct {E S : Ellipsoid n} (h : E.isequal S) :
    E.construct = S.construct := by -- --- PROOF ---
  obtain ⟨e, hq, hG⟩ := h
  obtain ⟨k₁, q₁, G₁⟩ := E
  obtain ⟨k₂, q₂, G₂⟩ := S
  simp only at e hq hG
  subst e hq
  have : G₁ = G₂ := funext fun i => funext fun j => hG i j
  subst this
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
