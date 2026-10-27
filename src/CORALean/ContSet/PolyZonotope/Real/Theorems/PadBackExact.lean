module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.PadBackPoint

@[expose] public section

/-!
# Padding the factor list moves no set

[1, Prop. 1] at positional factor identity. CORA's `mergeID` brings two SPZs to a common
identifier vector: it extends one exponent matrix with all-zero rows and permutes the other's
rows into the merged order. Here a factor *is* its row index, so what is left of `mergeID` is
the padding, and `padBack` is it. The claim Prop. 1 attaches is that each adjusted SPZ denotes
the original set. `padBack_point` is the forward half; the reverse inclusion is where the
padding is paid for, an appended factor no monomial reads being free to take any value. `padFront`
is the mirror image and needs no second statement.

## Inputs
* `r` – number of added factors
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the padded set equals the original

## References

* [1] [N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set Representation for
      Reachability Analysis". IEEE Transactions on Automatic Control,
      2021.](../../../../../../references/2021/kochdumper-tac-sparse-polyzonotopes.md)
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set over `p + r` factors is the set over `p`: the appended rows stand at
exponent zero, and the center and both generator blocks never moved. -/
theorem PolyZonotope.padBack_exact (r : ℕ) (pZ : PolyZonotope α) : -- --- CONCL ---
    pZ.construct = (pZ.padBack r).construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    -- the appended factors are given the value `0`, which no monomial reads
    have hpt : (pZ.padBack r).point (Fin.append a fun _ : Fin r => (0 : ℝ)) = pZ.point a := by
      rw [PolyZonotope.padBack_point]
      exact congrArg _ (funext fun k => Fin.append_left _ _ k)
    refine ⟨Fin.append a fun _ => 0, β, ?_, hβ, ?_⟩
    · refine Fin.addCases (fun k => ?_) (fun k => ?_)
      · rw [Fin.append_left]; exact ha k
      · rw [Fin.append_right, abs_zero]; exact zero_le_one
    · show pZ.point a + ∑ j, β j • pZ.GI j
          = (pZ.padBack r).point (Fin.append a fun _ => 0) + ∑ j, β j • pZ.GI j
      rw [hpt]
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    refine ⟨a ∘ Fin.castAdd r, β, fun k => ha _, hβ, ?_⟩
    -- the other way the factor vector is simply read at the half it was written against
    show (pZ.padBack r).point a + ∑ j, β j • pZ.GI j
        = pZ.point (a ∘ Fin.castAdd r) + ∑ j, β j • pZ.GI j
    rw [PolyZonotope.padBack_point]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
