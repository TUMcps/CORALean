module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Isequal

@[expose] public section

/-!
# Ellipsoids passing `isequal` denote the same set

`isequal` compares the shape matrices and the centers, which is all `construct` reads.

## Inputs
* `E` – ellipsoid
* `S` – ellipsoid

## Hypotheses
* `h` – `E` and `S` are `isequal`

## Conclusion
* `E` and `S` denote the same set
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isequal_construct {E S : Ellipsoid n} (h : E.isequal S) : -- --- CONCL ---
    E.construct = S.construct := by -- --- PROOF ---
  obtain ⟨hQ, hq⟩ := h
  obtain ⟨Q₁, q₁, h₁⟩ := E
  obtain ⟨Q₂, q₂, h₂⟩ := S
  simp only at hQ hq
  subst hQ hq
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
