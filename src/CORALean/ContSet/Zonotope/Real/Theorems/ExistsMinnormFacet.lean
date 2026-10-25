module

public import CORALean.ContSet.Zonotope.Real.Operations.Minnorm
public import CORALean.ContSet.Zonotope.Real.Theorems.HRepEq

@[expose] public section

/-!
# `minnorm` is attained

For a zonotope whose generators span the space, some selection of `n` generators has a nonzero
cross product (otherwise every halfspace is trivial and `hRep_eq` [1, Thm. 2] makes the zonotope
the whole space, which is bounded), and the offsets over the finitely many selections attain
their minimum.

## Inputs
* `Z` – zonotope

## Hypotheses
* `hspan` – generators span the space

## Conclusion
* some facet attains the smallest norm

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794, 2015.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.exists_minnormFacet (Z : Zonotope (Vec ℝ (n + 1)))
    (hspan : Submodule.span ℝ (Set.range Z.G) = ⊤) : -- --- CONCL ---
    ∃ S : Fin n → Fin Z.h,
      Z.facetNormal S ≠ 0 ∧ Z.minnormOffset S = Z.minnorm := by -- --- PROOF ---
  have hne : ∃ S : Fin n → Fin Z.h, Z.facetNormal S ≠ 0 := by
    by_contra hall
    push Not at hall
    -- every halfspace is trivial, so a far point on the first axis is in the zonotope
    set t : ℝ := ∑ υ, |Z.G υ 0| + 1 with ht
    have hmem : Z.c + Pi.single 0 t ∈ Z.construct := by
      rw [Zonotope.hRep_eq Z hspan]
      intro S
      simp [hall S]
    obtain ⟨β, hβ, hx⟩ := hmem
    have h0 := congrFun hx 0
    simp only [Pi.add_apply, Pi.single_eq_same, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      add_right_inj] at h0
    have : t ≤ ∑ υ, |Z.G υ 0| := by
      rw [h0]
      refine le_trans (Finset.sum_le_sum fun υ _ => le_abs_self _) ?_
      refine Finset.sum_le_sum fun υ _ => ?_
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hβ υ) |>.trans' (by rw [mul_comm])
    linarith
  -- the offsets over the finitely many selections attain their infimum
  obtain ⟨S₀, hS₀⟩ := hne
  have hfin : (Z.minnormOffset '' {S | Z.facetNormal S ≠ 0}).Finite :=
    (Set.toFinite _).image _
  have hnonempty : (Z.minnormOffset '' {S | Z.facetNormal S ≠ 0}).Nonempty :=
    ⟨_, ⟨S₀, hS₀, rfl⟩⟩
  have hmem := hnonempty.csInf_mem hfin
  obtain ⟨S, hS, hSeq⟩ := hmem
  exact ⟨S, hS, hSeq⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
