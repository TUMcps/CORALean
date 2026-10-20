module

public import CORALean.ContSet.ProbZonotope.Float.Operations.RepresentsaEmptySet

@[expose] public section

/-!
# `ProbZonotope.representsaEmptySet` is sound

A `true` answer exhibits a covariance entry whose interval is crossed, so the interval holds no
matrix and the family of laws is empty.

## Inputs
* `P` – probabilistic zonotope

## Hypotheses
* `h` – `P.representsaEmptySet` holds

## Conclusion
* `P.laws = ∅`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.representsaEmptySet_sound {P : ProbZonotope 𝕋 n}
    (h : P.representsaEmptySet = true) : -- --- CONCL ---
    P.laws = ∅ := by -- --- PROOF ---
  obtain ⟨i, -, hi⟩ := List.any_eq_true.1 h
  obtain ⟨j, -, hj⟩ := List.any_eq_true.1 hi
  have hlt := toReal_lt_of_ltStrict hj
  refine Set.eq_empty_of_forall_notMem fun m hm => ?_
  -- a law needs a covariance matrix in the interval, its `(i, j)` entry would lie in a crossed one
  obtain ⟨μ, -, S, hS, -⟩ := hm
  have h1 : toReal (P.cov.inf i j) ≤ S i j := (hS (i, j)).1
  have h2 : S i j ≤ toReal (P.cov.sup i j) := (hS (i, j)).2
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
