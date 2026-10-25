module

public import CORALean.Specification.STL.Definitions.Transformation
public import CORALean.Specification.STL.Theorems.SatOfPform

@[expose] public section

/-!
# A sound and complete transformation fixes non-temporal formulas

[1, Eq. 10]: `Υ(ϱ) ≡ Aϱ`, on every class of reach sequences `Υ` is sound and complete
for. The paper's proof reads the values of `R(0)` off a trace through each, so every `R(t)` must
be non-empty.

## Inputs
* `𝓡` – set of reach sequences
* `Υ` – transformation of formulas
* `ϱ` – predicate
* `R` – reach sequence

## Hypotheses
* `hs` – the transformation is sound
* `hc` – the transformation is complete
* `hne` – all reach sets are nonempty
* `hR` – the reach sequence is in the set

## Conclusion
* the transformation of a non-temporal formula is the atom

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.upsilon_ofPform {𝓡 : Set (ℝ≥0 → Set X)} {Υ : STL.Formula X → RTL.Formula X}
    (hs : STL.IsSound 𝓡 Υ) (hc : STL.IsComplete 𝓡 Υ)
    (hne : ∀ R ∈ 𝓡, ∀ t, (R t).Nonempty) (ϱ : Pform X) {R : ℝ≥0 → Set X}
    (hR : R ∈ 𝓡) : -- --- CONCL ---
    (Υ (STL.Formula.ofPform ϱ)).Satisfies R ↔ (RTL.Formula.A ϱ).Satisfies R := by -- --- PROOF ---
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
