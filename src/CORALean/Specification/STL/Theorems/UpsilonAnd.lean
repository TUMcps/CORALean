import CORALean.Specification.STL.Definitions.Transformation
import CORALean.Specification.STL.Theorems.SatAnd

/-!
# A sound and complete transformation distributes over conjunction

[1, Eq. 11]: `Υ(φ₁ ∧ φ₂) ≡ Υ(φ₁) ∧ Υ(φ₂)`, on every class of reach sequences `Υ` is sound
and complete for.

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

theorem STL.upsilon_and {𝓡 : Set (ℝ≥0 → Set X)} {Υ : STL.Formula X → RTL.Formula X}
    (hs : STL.IsSound 𝓡 Υ) (hc : STL.IsComplete 𝓡 Υ) (φ₁ φ₂ : STL.Formula X)
    {R : ℝ≥0 → Set X} (hR : R ∈ 𝓡) :
    (Υ (φ₁.and φ₂)).Sat R ↔ (RTL.Formula.and (Υ φ₁) (Υ φ₂)).Sat R := by -- --- PROOF ---
  constructor
  · intro h
    have h' := hs R hR _ h
    -- each conjunct holds of every trace, hence `Υ` of it by completeness
    exact ⟨hc R hR φ₁ fun ξ hξ => ((STL.Formula.sat_and _ _ _).1 (h' ξ hξ)).1,
      hc R hR φ₂ fun ξ hξ => ((STL.Formula.sat_and _ _ _).1 (h' ξ hξ)).2⟩
  · rintro ⟨h₁, h₂⟩
    refine hc R hR _ fun ξ hξ => (STL.Formula.sat_and _ _ _).2 ?_
    exact ⟨hs R hR _ h₁ ξ hξ, hs R hR _ h₂ ξ hξ⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
