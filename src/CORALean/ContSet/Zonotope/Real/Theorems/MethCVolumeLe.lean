module

public import CORALean.ContSet.Zonotope.Real.Operations.MethCBasis

@[expose] public section

/-!
# The `methC` search returns a maximizer

What the exhaustive search is proved to deliver, and the only optimality claim made about `methC`:
among the `n`-selections of what the length filter left, none spans more volume than the basis
returned. It is by construction (`exists_max_image`), and worth stating because a reader would
otherwise assume more. It does not say that the enclosure is the tightest, that the length filter
kept the right candidates, or that maximizing `|det|` minimizes anything. Soundness owes none of
it — `reduceByBasis_outer` holds at every invertible basis. The hypothesis is CORA's own
precondition: with fewer than `n` candidates there is nothing to select, and `methCBasis` answers
`1` without searching.

## Inputs
* `Z` – zonotope
* `part` – split of the generators
* `e` – selection of filtered generators

## Hypotheses
* `h` – enough filtered generators

## Conclusion
* no selection spans more volume than the returned basis
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- No selection of `n` filtered generators spans more volume than the basis
the search returns. -/
theorem Zonotope.methCVolume_le (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (h : n ≤ min (n + 8) r)
    (e : Fin n ↪ Fin (min (n + 8) r)) :
    Z.methCVolume part e ≤ |(Z.methCBasis part).det| := by
  unfold Zonotope.methCBasis
  rw [dif_pos h]
  exact (Finset.exists_max_image Finset.univ (Z.methCVolume part)
    ⟨Fin.castLEEmb h, Finset.mem_univ _⟩).choose_spec.2 e (Finset.mem_univ e)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
