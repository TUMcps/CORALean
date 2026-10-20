module

public import CORALean.ContSet.Zonotope.Real.Operations.MethCVolume

@[expose] public section

/-!
# `Zonotope.methCBasis`

Stage two of `methC`: an exhaustive search over every `n`-selection of what the length filter
left, answering with the one of largest spanned volume. Total and terminating without a fuel
bound — `Fin n ↪ Fin (min (n + 8) r)` is a finite type, so the search is a maximum over a
`Finset`, noncomputable as every real-ranked choice here. CORA keeps `filterLength(2) = n + 3`
candidates and picks by zonotope volume [1]; this is its code path at `rem = 1`, a single-entry
shortlist. `methC_volume_le` is what the search delivers; nothing claims the enclosure is
tightest. Fewer than `n` candidates leaves nothing to select: the answer is `1`, which boxes along
the axes (`reduceBy`).

## Inputs
* `Z` – zonotope
* `part` – split of the generators

## Output
* basis of the filtered generators of largest volume

## References

* [1] `contSet/@zonotope/private/priv_reduceMethC.m`, CORA (Sep. 2025). No
      paper behind the rule was confirmed.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `n` filtered generators of largest spanned volume, as the matrix whose
columns they are, or `1` where the filter left fewer than `n` to choose from. -/
noncomputable def Zonotope.methCBasis (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : Mat ℝ n n :=
  if h : n ≤ min (n + 8) r then
    Matrix.of fun i k => Z.G (Z.methCFilter part
      ((Finset.exists_max_image Finset.univ (Z.methCVolume part)
        ⟨Fin.castLEEmb h, Finset.mem_univ _⟩).choose k)) i
  else 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
