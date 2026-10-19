module

public import CORALean.ContSet.Capsule.Real.Operations.Reindex
public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# `Capsule.reindex` is exactly the relabelled set

The Euclidean distance is a sum over all coordinates, and a relabelling of the index permutes the
summands, so the relabelled capsule denotes precisely the image of the original under
`reindexLin e`. An equality, as `Reindex` asks.

## Inputs
* `n` – source dimension
* `m` – target dimension
* `e` – index bijection
* `C` – capsule

## Hypotheses
* none

## Conclusion
* `reindex` is the exact image
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.reindex_exact {n m : ℕ} (e : Fin m ≃ Fin n) (C : Capsule n) :
    (C.reindex e).construct = reindexLin e '' C.construct := by -- --- PROOF ---
  have key : ∀ (y : Vec ℝ m) (t : ℝ),
      ∑ i, (y i - ((C.reindex e).c i + t * (C.reindex e).g i)) ^ 2
        = ∑ j, (y (e.symm j) - (C.c j + t * C.g j)) ^ 2 := by
    intro y t
    rw [← Equiv.sum_comp e (fun j => (y (e.symm j) - (C.c j + t * C.g j)) ^ 2)]
    simp [Capsule.reindex]
  ext y
  constructor
  · rintro ⟨t, ht, hy⟩
    refine ⟨fun j => y (e.symm j), ⟨t, ht, ?_⟩, funext fun i => by simp [reindexLin]⟩
    rw [key] at hy
    exact hy
  · rintro ⟨x, ⟨t, ht, hx⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    rw [key]
    have h2 : ∀ j, (reindexLin e x) (e.symm j) = x j := fun j => by simp [reindexLin]
    simp only [h2]
    exact hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
