module

public import CORALean.ContSet.Zonotope.Float.Operations.Pick
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# Picking the generators of a zonotope encloses

If the index map is injective and the generators it leaves out are zero, a point at the
coefficients `β` keeps its value: the picked sum is the whole sum, the others adding zero.
Otherwise `pick` returns the zonotope.

## Inputs
* `Z` – zonotope
* `m` – number of generators picked
* `idx` – the index of the generator behind each

## Hypotheses
* none

## Conclusion
* the zonotope is contained in the picked one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.pick_outer (Z : Zonotope (Vec 𝕋 n)) (m : ℕ) (idx : Fin m → ℕ) : -- --- CONCL ---
    Z.toSet ⊆ (Z.pick m idx).toSet := by -- --- PROOF ---
  unfold Zonotope.pick
  split_ifs with hv
  swap
  · exact subset_rfl
  obtain ⟨hlt, hinj, hzero⟩ := hv
  set idx' : Fin m → Fin Z.h := fun t => ⟨idx t, hlt t⟩ with hidx'
  have hinj' : Function.Injective idx' := fun s t hst => hinj (congrArg Fin.val hst)
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_nominalSet_iff.mp hz
  -- the coefficients of the picked generators
  refine ⟨z, Zonotope.mem_nominalSet_iff.mpr ⟨fun t => β (idx' t), fun t => hβ _, fun i => ?_⟩,
    e, he, rfl⟩
  rw [hx i]
  congr 1
  show _ = ∑ t, toReal (Z.G (idx' t) i) * β (idx' t)
  rw [← Finset.sum_image (f := fun l => toReal (Z.G l i) * β l) (fun x _ y _ hxy => hinj' hxy)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun l _ hl => ?_).symm
  have hl' : ¬ ∃ t, idx t = l.val := fun ⟨t, ht⟩ =>
    hl (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, Fin.ext ht⟩)
  obtain ⟨h1, h2⟩ := hzero l hl' i
  have : toReal (Z.G l i) = 0 :=
    le_antisymm (by simpa [toReal_zero] using toReal_le_of_le h1)
      (by simpa [toReal_zero] using toReal_le_of_le h2)
  rw [this, zero_mul]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
