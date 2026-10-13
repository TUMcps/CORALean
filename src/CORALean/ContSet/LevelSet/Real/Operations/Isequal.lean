module

public import CORALean.ContSet.LevelSet.Real.Operations.Compact

@[expose] public section

/-!
# `LevelSet.isequal`

CORA's `@levelSet/isequal` at two level sets (`aux_isequal_levelSet`): both are compacted
(`compact_(ls,'all',eps)`), then every row of the first must find an unused row of the second
with the same operator and an equation that `simplify` shows equal after the variables used
are renamed. The renaming is a symbolic matter, so here the rows are matched under the identity
renaming, the equation as a function: the second level set is the first with its rows
permuted. That is stricter than CORA, which also accepts a renaming of the variables (and
accepts too many, see `Theorems/IsequalCoraCounterexample`), and the tolerance `tol` is not
modelled. A level set that compacts to `emptySet` is outside CORA's `aux_isequal_levelSet`
(its `ls.eq` read fails) and is `False` here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def LevelSet.isequal (L S : LevelSet n) : Prop :=
  match L.compact_, S.compact_ with
  | Sum.inl L', Sum.inl S' =>
      ∃ σ : Fin L'.m → Fin S'.m, Function.Bijective σ ∧
        ∀ i, L'.op i = S'.op (σ i) ∧ ∀ x, L'.f x i = S'.f x (σ i)
  | _, _ => False


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
