module

public import CORALean.ContSet.LevelSet.Real.Operations.Compact

@[expose] public section

/-!
# `LevelSet.isequal`

CORA's `@levelSet/isequal` (`aux_isequal_levelSet`): both level sets are compacted, then every row
of the first must find an unused row of the second with the same operator and an equation that
`simplify` shows equal after the variables used are renamed. The renaming is symbolic, so here the
rows are matched under the identity renaming: the second level set is the first with its rows
permuted. That is stricter than CORA, which accepts a renaming of the variables (and too many, see
`Theorems/IsequalCoraCounterexample`); the tolerance `tol` is not modelled. A level set that
compacts to `emptySet` is outside CORA's `aux_isequal_levelSet` and is `False` here.

## Inputs
* `L` – level set
* `S` – level set

## Output
* the rows of `S` are those of `L` permuted
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LevelSet.isequal (L S : LevelSet n) : Prop :=
  match L.compact_, S.compact_ with
  | Sum.inl L', Sum.inl S' =>
      ∃ σ : Fin L'.m → Fin S'.m, Function.Bijective σ ∧
        ∀ i, L'.op i = S'.op (σ i) ∧ ∀ x, L'.f x i = S'.f x (σ i)
  | _, _ => False


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
