import CORALean.Specification.STL.STL

/-!
# Rewriting, `G_I` of a disjunction

[1, Table 1] `G_I(φ₁ ∨ φ₂) ⇐ G_I φ₁ ∨ G_I φ₂`.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.rewrite_globOpen_or (φ₁ φ₂ : STL.Formula X) (ξ : ℝ≥0 → X)
    (h : ((STL.Formula.globOpen 1 φ₁).or (STL.Formula.globOpen 1 φ₂)).Sat ξ) :
    (STL.Formula.globOpen 1 (φ₁.or φ₂)).Sat ξ := by
  simp only [STL.Formula.Sat] at h ⊢
  rcases h with h | h
  · exact fun t h₀ h₁ => Or.inl (h t h₀ h₁)
  · exact fun t h₀ h₁ => Or.inr (h t h₀ h₁)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
