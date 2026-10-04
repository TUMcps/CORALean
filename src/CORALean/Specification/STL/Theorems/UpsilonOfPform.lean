import CORALean.Specification.STL.Definitions.Transformation
import CORALean.Specification.STL.Theorems.SatOfPform

/-!
# A sound and complete transformation fixes non-temporal formulas

[1, Eq. 10]: `Υ(ϱ) ≡ Aϱ`, on every class of reach sequences `Υ` is sound and complete
for. The paper's proof reads the values of `R(0)` off a trace through each, so every `R(t)` must
be non-empty.

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

theorem STL.upsilon_ofPform {𝓡 : Set (ℝ≥0 → Set X)} {Υ : STL.Formula X → RTL.Formula X}
    (hs : STL.IsSound 𝓡 Υ) (hc : STL.IsComplete 𝓡 Υ)
    (hne : ∀ R ∈ 𝓡, ∀ t, (R t).Nonempty) (ϱ : Pform X) {R : ℝ≥0 → Set X} (hR : R ∈ 𝓡) :
    (Υ (STL.Formula.ofPform ϱ)).Sat R ↔ (RTL.Formula.A ϱ).Sat R := by -- --- PROOF ---
  constructor
  · intro h r hr
    -- extend `r ∈ R 0` to a trace of `C(R)`, using a value at every other time
    classical
    let ξ : ℝ≥0 → X := fun t => if t = 0 then r else (hne R hR t).some
    have hξ : ξ ∈ ReachSequence.traceSet R := by
      intro t
      by_cases ht : t = 0
      · subst ht; simpa [ξ] using hr
      · simpa [ξ, ht] using (hne R hR t).some_mem
    have := (STL.Formula.sat_ofPform ϱ ξ).1 (hs R hR _ h ξ hξ)
    simpa [ξ] using this
  · intro h
    refine hc R hR _ fun ξ hξ => ?_
    exact (STL.Formula.sat_ofPform ϱ ξ).2 (h _ (hξ 0))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
