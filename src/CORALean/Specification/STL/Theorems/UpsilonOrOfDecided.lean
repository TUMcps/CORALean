module

public import CORALean.Specification.STL.Definitions.Transformation
public import CORALean.Specification.STL.Definitions.Tsupp
public import CORALean.Specification.STL.Theorems.SatOr

@[expose] public section

/-!
# A sound and complete transformation distributes over disjunction of independent formulas

[1, Eq. 12]'s proof: if `Υ(ϕ₁ ∨ ϕ₂)` held but neither `C(R) ⊨ₜ ϕ₁` nor `C(R) ⊨ₜ ϕ₂`, there are
traces `ξ₁`, `ξ₂` in `C(R)` violating one each; since `C(R)` is a product of the sets `R(t)`,
the trace that is `ξ₁` on the time set of `ϕ₁` and `ξ₂` elsewhere is in `C(R)` and violates both.
That needs `ϕᵢ` to be settled by the trace on its own time set `Tᵢ`, the two disjoint
(`IsDecidedOn`); the printed hypothesis is `tsupp(ϕ₁) ∩ tsupp(ϕ₂) = ∅`, which gives it only if
`tsupp(ϕᵢ)` decides `ϕᵢ`.

## Inputs
* `𝓡` – set of reach sequences
* `Υ` – transformation of formulas
* `φ₁` – left formula
* `φ₂` – right formula
* `T₁` – time set deciding the left formula
* `T₂` – time set deciding the right formula
* `R` – reach sequence

## Hypotheses
* `hs` – the transformation is sound
* `hc` – the transformation is complete
* `hT` – the time sets are disjoint
* `h₁` – the time set decides the left formula
* `h₂` – the time set decides the right formula
* `hR` – the reach sequence is in the set

## Conclusion
* the transformation of a disjunction is the disjunction of the transformations

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and Hybrid
      Systems". Automated Technology for Verification and Analysis, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 12]: `Υ(ϕ₁ ∨ ϕ₂) ≡ Υ(ϕ₁) ∨ Υ(ϕ₂)` when `ϕ₁`, `ϕ₂` are decided by disjoint time sets. -/
theorem STL.upsilon_or_of_decided {𝓡 : Set (ℝ≥0 → Set X)} {Υ : STL.Formula X → RTL.Formula X}
    (hs : STL.IsSound 𝓡 Υ) (hc : STL.IsComplete 𝓡 Υ) (φ₁ φ₂ : STL.Formula X)
    {T₁ T₂ : Set ℝ≥0} (hT : Disjoint T₁ T₂) (h₁ : φ₁.IsDecidedOn T₁) (h₂ : φ₂.IsDecidedOn T₂)
    {R : ℝ≥0 → Set X} (hR : R ∈ 𝓡) : -- --- CONCL ---
    (Υ (φ₁.or φ₂)).Satisfies R ↔ (RTL.Formula.or (Υ φ₁) (Υ φ₂)).Satisfies R := by -- --- PROOF ---
  constructor
  · intro h
    have hor := hs R hR _ h
    -- if neither disjunct holds of all traces, splice two violating traces of `C(R)`
    by_contra hno
    have hn1 : ¬ φ₁.HoldsOn (ReachSequence.traceSet R) := fun h1 => hno (Or.inl (hc R hR φ₁ h1))
    have hn2 : ¬ φ₂.HoldsOn (ReachSequence.traceSet R) := fun h2 => hno (Or.inr (hc R hR φ₂ h2))
    simp only [STL.Formula.HoldsOn, not_forall] at hn1 hn2
    obtain ⟨ξ₁, hξ₁, hv₁⟩ := hn1
    obtain ⟨ξ₂, hξ₂, hv₂⟩ := hn2
    classical
    -- the splice: `ξ₁` on `T₁`, `ξ₂` elsewhere, a trace of `C(R)` violating both
    set ξ : ℝ≥0 → X := fun t => if t ∈ T₁ then ξ₁ t else ξ₂ t with hξ
    have hmem : ξ ∈ ReachSequence.traceSet R := fun t => by
      by_cases ht : t ∈ T₁
      · simp only [hξ, if_pos ht]; exact hξ₁ t
      · simp only [hξ, if_neg ht]; exact hξ₂ t
    -- it agrees with `ξ₁` on `T₁` and with `ξ₂` on `T₂`, so it violates both
    have hv1 : ¬ φ₁.Satisfies ξ := fun h' =>
      hv₁ ((h₁ ξ ξ₁ fun t ht => by simp only [hξ, if_pos ht]).1 h')
    have hv2 : ¬ φ₂.Satisfies ξ := fun h' =>
      hv₂ ((h₂ ξ ξ₂ fun t ht => by
        have : t ∉ T₁ := fun h1 => Set.disjoint_left.1 hT h1 ht
        simp only [hξ, if_neg this]).1 h')
    rcases (STL.Formula.sat_or _ _ _).1 (hor ξ hmem) with h' | h'
    · exact hv1 h'
    · exact hv2 h'
  · rintro (h | h)
    · exact hc R hR _ fun ξ hξ => (STL.Formula.sat_or _ _ _).2 (Or.inl (hs R hR _ h ξ hξ))
    · exact hc R hR _ fun ξ hξ => (STL.Formula.sat_or _ _ _).2 (Or.inr (hs R hR _ h ξ hξ))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
