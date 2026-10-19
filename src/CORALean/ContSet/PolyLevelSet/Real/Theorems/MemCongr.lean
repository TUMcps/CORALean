module

public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet

@[expose] public section

/-!
# Rows that read the same

Two systems with the same right-hand sides and operators, whose polynomial parts agree at two
points, hold at both or at neither. This is what an operation that rewrites the monomials and keeps
the rows, as `compact` does or as dropping unread variables does, needs.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n n' : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The rows of `P` rewritten over other monomials, on a box `D'`, hold at `x'` exactly when `P`'s
hold at `x`, if both polynomial parts take the same value there and `x'` is in `D'` iff `x` in
`P.dom`. -/
theorem PolyLevelSet.mem_congr (P : PolyLevelSet n) {q' : ℕ} {A' : Mat ℝ P.m q'}
    {R' : Fin n' → Fin q' → ℕ} {D' : Interval (Vec ℝ n')} {x : Vec ℝ n} {x' : Vec ℝ n'}
    (h : A' *ᵥ PolyZonotope.monomial R' x' = P.A *ᵥ PolyZonotope.monomial P.R x)
    (hD : x' ∈ D'.construct ↔ x ∈ P.dom.construct) : -- --- CONCL ---
    x' ∈ (⟨P.m, q', A', R', P.b, P.op, D'⟩ : PolyLevelSet n').construct
      ↔ x ∈ P.construct := by -- --- PROOF ---
  show (x' ∈ D'.construct ∧ ∀ i, (P.op i).holds ((A' *ᵥ PolyZonotope.monomial R' x' - P.b) i)) ↔ _
  rw [h, hD]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
