module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Pick
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# Picking generators encloses

If the index map is injective and the generators it leaves out are zero, a point at the factors
`a` keeps its value: the sum over the picked generators is the sum over all, the others adding
zero. Otherwise `pick` returns the set.

## Inputs
* `pZ` – polynomial zonotope
* `m` – number of generators picked
* `idx` – the generator behind each

## Hypotheses
* none

## Conclusion
* the set is contained in the picked one
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

theorem PolyZonotope.pick_outer (pZ : PolyZonotope (Vec 𝕋 n)) (m : ℕ)
    (idx : Fin m → ℕ) : -- --- CONCL ---
    pZ.toSet ⊆ (pZ.pick m idx).toSet := by -- --- PROOF ---
  unfold PolyZonotope.pick
  split_ifs with hv
  swap
  · exact subset_rfl
  obtain ⟨hlt, hinj, hzero⟩ := hv
  -- the generators as `Fin pZ.h` indices
  set idx' : Fin m → Fin pZ.h := fun t => ⟨idx t, hlt t⟩ with hidx'
  have hinj' : Function.Injective idx' := fun s t hst => hinj (congrArg Fin.val hst)
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_nominalSet_iff.mp hz
  refine ⟨z, PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun i => ?_⟩, e, he, rfl⟩
  rw [hx i]
  congr 2
  -- the picked sum is the whole sum: the generators left out add zero
  show _ = ∑ t, toReal (pZ.G (idx' t) i) * Real.PolyZonotope.monomial pZ.E a (idx' t)
  rw [← Finset.sum_image (f := fun l => toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l)
    (fun x _ y _ hxy => hinj' hxy)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun l _ hl => ?_).symm
  have hl' : ¬ ∃ t, idx t = l.val := fun ⟨t, ht⟩ =>
    hl (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, Fin.ext ht⟩)
  obtain ⟨h1, h2⟩ := hzero l hl' i
  have : toReal (pZ.G l i) = 0 :=
    le_antisymm (by simpa [toReal_zero] using toReal_le_of_le h1)
      (by simpa [toReal_zero] using toReal_le_of_le h2)
  rw [this, zero_mul]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
