module

public import CORALean.ContSet.Zonotope.Real.Operations.SplitCora
public import CORALean.ContSet.Zonotope.Real.Operations.SplitFirstGen

@[expose] public section

/-!
# `Zonotope.splitFirstGenCora`: `splitFirstGen` as CORA's code runs

`@zonotope/splitFirstGen.m` (l. 39-42) takes `index` as the argmax of `norm(G(:,j)'*G,1)` over the
generators of the original zonotope and calls `split(Z{i}, index)`, which reads it as a generator
of the bounding box (see `Zonotope.splitCora`). For the generators `(1,0), (0,1), (1,1)` it picks
`3` and the box has two. Read from the source, not run; the empty generator list is not modelled.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `splitFirstGen` for one zonotope, `index` counted from `1`; `none` is the error. -/
noncomputable def Zonotope.splitFirstGenCora (Z : Zonotope (Vec ℝ n)) :
    Option (Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n)) :=
  let h := fun j => ∑ k, |Z.G j ⬝ᵥ Z.G k|
  match (List.finRange Z.h).argmax h with
  | some j => Z.splitCora (j.val + 1)
  | none => none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
