import CORALean.Specification.STL.STL

/-!
# Rewriting, `F_I` of a disjunction

[1, Table 1] `F_I(φ₁ ∨ φ₂) ⇐ F_I φ₁ ∨ F_I φ₂`.

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

theorem STL.rewrite_finOpen_or (φ₁ φ₂ : STL.Formula X) (ξ : ℝ≥0 → X)
    (h : ((STL.Formula.finOpen 1 φ₁).or (STL.Formula.finOpen 1 φ₂)).Sat ξ) :
    (STL.Formula.finOpen 1 (φ₁.or φ₂)).Sat ξ := by
  simp only [STL.Formula.Sat] at h ⊢
  rcases h with ⟨s, hs₀, hs₁, hs⟩ | ⟨s, hs₀, hs₁, hs⟩
  · exact ⟨s, hs₀, hs₁, Or.inl hs⟩
  · exact ⟨s, hs₀, hs₁, Or.inr hs⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
