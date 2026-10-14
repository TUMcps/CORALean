module

public import CORALean.ContSet.Capsule.Real.Operations.Project

@[expose] public section

/-!
# `Capsule.project` is exactly the projected set

For distinct `dims`, the image of a capsule under the coordinate selection is the smaller
capsule: dropping coordinates only shrinks the Euclidean distance (the inclusion), and the dropped
coordinates of a point can be put on the segment, where they cost nothing (the reverse). A repeated
coordinate in `dims` is an equality constraint the capsule does not carry, and the image is then a
proper subset of the projected capsule, so injectivity is a hypothesis; CORA does not check it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.project_exact (C : Capsule n) {dims : Fin m → Fin n}
    (hd : Function.Injective dims) :
    (C.project dims).construct =
      (fun x : Vec ℝ n => fun i => x (dims i)) '' C.construct := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨t, ht, hy⟩
    classical
    -- the preimage point: `y` at `dims`, the segment point `s` elsewhere
    set s : Vec ℝ n := fun j => C.c j + t * C.g j with hs
    refine ⟨Function.extend dims y s, ⟨t, ht, ?_⟩, funext fun i => hd.extend_apply _ _ _⟩
    refine le_trans (le_of_eq ?_) hy
    congr 1
    -- outside the range of `dims` the new point is on the segment, contributing nothing
    have hout : ∀ j ∈ (Finset.univ : Finset (Fin n)), j ∉ Finset.univ.image dims →
        (Function.extend dims y s j - s j) ^ 2 = 0 := by
      intro j _ hj
      have : ¬ ∃ i, dims i = j := fun ⟨i, hi⟩ =>
        hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
      rw [Function.extend_apply' _ _ _ this, sub_self]; ring
    -- the sum over all coordinates is the sum over the image of `dims`, which is injective
    rw [← Finset.sum_subset (Finset.subset_univ _) (fun j hj hnot => hout j hj hnot),
      Finset.sum_image (fun a _ b _ h => hd h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hd.extend_apply, hs, Capsule.project]
  · -- dropping coordinates only shrinks the squared distance
    rintro ⟨x, ⟨t, ht, hx⟩, rfl⟩
    refine ⟨t, ht, le_trans (Real.sqrt_le_sqrt ?_) hx⟩
    classical
    have := Finset.sum_image (f := fun j => (x j - (C.c j + t * C.g j)) ^ 2)
      (s := (Finset.univ : Finset (Fin m))) (g := dims) (fun a _ b _ h => hd h)
    simp only [Capsule.project]
    rw [← this]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
