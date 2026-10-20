module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Partition
public import CORALean.Global.Sort
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-!
# `Zonotope.methCFilter`

Stage one of CORA's `methC` [1]: the dropped generators are ranked by length and only the
longest `n + 8` are kept as candidates — `filterLength(1)`, CORA's default, clamped to how many
there are. Without it stage two would search every `n`-subset of everything dropped. Length is
measured after normalizing each coordinate by that row's `1`-norm over all generators — CORA's
`W`, and `pinv(W)` where a row is identically zero, which division in Lean already is. Squaring
is monotone, so the ranking is `priv_lengthFilter`'s `vecnorm` and the float layer would need no
square root, as for Combastel's rule.

## Inputs
* `Z` – zonotope
* `part` – split of the generators
* `k` – rank in the filter

## Output
* index of the `k`-th longest dropped generator

## References

* [1] `contSet/@zonotope/private/priv_reduceMethC.m` and `priv_lengthFilter.m`,
      CORA (Sep. 2025). No paper behind the rule was confirmed.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- CORA's `W`: what each coordinate's row of the generator matrix reaches in
`1`-norm, the diagonal the length filter measures against. -/
noncomputable def Zonotope.aux_methCScale (Z : Zonotope (Vec ℝ n)) (i : Fin n) : ℝ :=
  ∑ j, |Z.G j i|

/-- The length stage one ranks by, `‖W⁻¹g‖₂` squared. A zero row divides to
zero, which is where CORA's `pinv(W)` puts it too. -/
noncomputable def Zonotope.aux_methCLength (Z : Zonotope (Vec ℝ n)) (j : Fin Z.h) : ℝ :=
  ∑ i, (Z.G j i / Z.aux_methCScale i) ^ 2


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `min (n + 8) r` longest of the `r` dropped generators, named in
decreasing length: CORA's `priv_lengthFilter` at its default `n + 8`. Sorting
is ascending, so the length enters negated. -/
noncomputable def Zonotope.methCFilter (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (k : Fin (min (n + 8) r)) : Fin Z.h :=
  part.right ((Tuple.sort fun l => -Z.aux_methCLength (part.right l))
    (Fin.castLE (min_le_right (n + 8) r) k))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
