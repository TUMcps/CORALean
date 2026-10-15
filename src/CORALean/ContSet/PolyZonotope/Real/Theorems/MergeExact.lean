module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Merge
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MergePoint

@[expose] public section

/-!
# Joining equal exponent columns loses nothing

`merge` touches neither `p` nor `q`, so one factor vector reads both sides and
the two inclusions come out of the single equation below, exactly as they do
for `compactGens`. That equation is `merge_point` with the independent block
added back on either side, the center being `point`'s own first summand.

What is *not* claimed here is [1, Prop. 3.3]'s regularity — see `Merge.lean`.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

-- so both inclusions hold at the very same coefficients
theorem PolyZonotope.merge_exact (pZ : PolyZonotope α) :
    pZ.construct = pZ.merge.construct := by -- --- PROOF ---
  have key : ∀ (a : Fin pZ.p → ℝ) (β : Fin pZ.q → ℝ),
      pZ.c + (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i) + ∑ j, β j • pZ.GI j
        = pZ.c + (∑ j : Fin pZ.merge.h,
            PolyZonotope.monomial pZ.merge.E a j • pZ.merge.G j) + ∑ j, β j • pZ.GI j :=
    fun a β => congrArg (fun s => s + ∑ j, β j • pZ.GI j)
      (PolyZonotope.merge_point pZ a).symm
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, key a β⟩
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, (key a β).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
