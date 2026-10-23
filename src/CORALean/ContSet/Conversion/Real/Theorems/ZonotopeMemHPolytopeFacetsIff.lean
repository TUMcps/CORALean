module

public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_HPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# Membership in CORA's facet polytope of a zonotope

With some generator nonzero, the rows `[C; -C]` at `±C c + Σ |C G|` say exactly that every row
`v` of `C` has `|v ⬝ (x - c)| ≤ Σⱼ |v ⬝ Gⱼ|`: the two rows of a pair are the two sides of one
absolute value.

## Inputs
* `Z` – zonotope
* `x` – point

## Hypotheses
* `hG` – some generator is nonzero

## Conclusion
* point is in the facet polytope iff it meets every row bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point is in the facet polytope iff it meets every row's absolute bound. -/
theorem Zonotope.mem_hPolytopeFacets_iff (Z : Zonotope (Vec ℝ (m + 1)))
    (hG : ¬∀ j, Z.G j = 0) (x : Vec ℝ (m + 1)) : -- --- CONCL ---
    x ∈ Z.hPolytopeFacets.construct
      ↔ ∀ v ∈ Z.facetRows, |v ⬝ᵥ (x - Z.c)| ≤ ∑ j, |v ⬝ᵥ Z.G j| := by -- --- PROOF ---
  unfold Zonotope.hPolytopeFacets
  rw [if_neg hG, HPolytope.mem_ineqs_iff]
  -- the two halves of the stacked rows, one pair per row of `C`
  have hpair : ∀ k : Fin Z.facetRows.length,
      ((Fin.append (fun k => Z.facetRows.get k) (-fun k => Z.facetRows.get k) *ᵥ x)
          (Fin.castAdd _ k) ≤ Fin.append (fun k => Z.facetRows.get k ⬝ᵥ Z.c
            + ∑ j, |Z.facetRows.get k ⬝ᵥ Z.G j|)
            (fun k => -(Z.facetRows.get k ⬝ᵥ Z.c) + ∑ j, |Z.facetRows.get k ⬝ᵥ Z.G j|)
            (Fin.castAdd _ k)
        -- and the row `-C k` beside it
        ∧ (Fin.append (fun k => Z.facetRows.get k) (-fun k => Z.facetRows.get k) *ᵥ x)
          (Fin.natAdd _ k) ≤ Fin.append (fun k => Z.facetRows.get k ⬝ᵥ Z.c
            + ∑ j, |Z.facetRows.get k ⬝ᵥ Z.G j|)
            (fun k => -(Z.facetRows.get k ⬝ᵥ Z.c) + ∑ j, |Z.facetRows.get k ⬝ᵥ Z.G j|)
            (Fin.natAdd _ k))
      ↔ |Z.facetRows.get k ⬝ᵥ (x - Z.c)| ≤ ∑ j, |Z.facetRows.get k ⬝ᵥ Z.G j| := by
    -- read each side as a dot product with `C k`
    intro k
    simp only [mulVec, Fin.append_left, Fin.append_right, Pi.neg_apply, dotProduct_sub, abs_le]
    have e₀ : (fun j => Z.facetRows.get k j) ⬝ᵥ x = Z.facetRows.get k ⬝ᵥ x := rfl
    have e₁ : (fun j => -Z.facetRows.get k j) ⬝ᵥ x = -(Z.facetRows.get k ⬝ᵥ x) :=
      neg_dotProduct _ _
    rw [e₀, e₁]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  constructor
  · intro h v hv
    obtain ⟨k, rfl⟩ := List.get_of_mem hv
    exact (hpair k).mp ⟨h _, h _⟩
  · intro h i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · exact ((hpair k).mpr (h _ (List.get_mem _ _))).1
    · exact ((hpair k).mpr (h _ (List.get_mem _ _))).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
