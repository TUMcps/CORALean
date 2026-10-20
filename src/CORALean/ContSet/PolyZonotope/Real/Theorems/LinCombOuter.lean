module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombValue
public import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter

@[expose] public section

/-!
# `linComb` contains every segment between the two polynomial zonotopes

The fresh factor takes `2λ - 1`, in `[-1,1]` exactly when `λ ∈ [0,1]`, and the two sets keep
their own factors, so the dependent part of the segment is reproduced, not enclosed. The
independent block is where something is given away: its coefficients come out as
`pairCoeffSum` and `pairCoeffDiff`, which record that the two sides share one `λ` but not that
the same `λ` drives the dependent part. So the containment is one-way, `_outer` rather than
`_exact` ([1, Prop. 15]); without an independent block it is the equality
`linComb_exact_of_dependent`. Nothing asks for convexity. The witness's value is `linComb_value`.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* none

## Conclusion
* every segment between the sets lies in the result

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   11-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.linComb_outer (pZ₁ pZ₂ : PolyZonotope α) :
    Set.linComb pZ₁.construct pZ₂.construct ⊆ (pZ₁.linComb pZ₂).construct := by -- --- PROOF ---
  rintro x ⟨y₁, ⟨a₁, β₁, ha₁, hβ₁, rfl⟩, y₂, ⟨a₂, β₂, ha₂, hβ₂, rfl⟩,
    lam, ⟨hl0, hl1⟩, rfl⟩
  refine ⟨Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1),
    Fin.append (Zonotope.pairCoeffSum β₁ β₂ lam) (Zonotope.pairCoeffDiff β₁ β₂ lam),
    ?_, ?_, ?_⟩
  -- the fresh factor is `2λ-1`, which stays in `[-1,1]` for `λ` in the unit interval
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro k
        simpa using ha₁ k
      · intro k
        simpa using ha₂ k
    · intro _
      simp only [Fin.append_right]
      rw [abs_le]
      constructor <;> linarith
  · refine Fin.addCases ?_ ?_
    · intro j
      simpa using Zonotope.abs_pairCoeffSum_le_one hβ₁ hβ₂ hl0 hl1 j
    · intro j
      simpa using Zonotope.abs_pairCoeffDiff_le_one hβ₁ hβ₂ hl0 hl1 j
  -- the value: `linComb_value`, the arithmetic this witness was chosen for
  · exact PolyZonotope.linComb_value pZ₁ pZ₂ a₁ β₁ a₂ β₂ lam

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
