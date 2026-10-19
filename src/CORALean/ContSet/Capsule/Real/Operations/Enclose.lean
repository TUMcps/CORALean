module

public import CORALean.ContSet.Capsule.Real.Operations.ConvHull
public import CORALean.ContSet.Capsule.Real.Operations.Mtimes

@[expose] public section

/-!
# `Capsule.enclose`

CORA's `@capsule/enclose.m` with a matrix: `C2 = M * Cplus`, then `convHull(C, C2)`. Read as
printed: the header documents `C2 = M*C + Cplus`, but the code multiplies `Cplus` and adds
nothing (see `Capsule.enclose_cora_counterexample`); `ContSet.enclose` is the documented set.

## Inputs
* `C` – capsule
* `M` – matrix
* `Cplus` – capsule mapped by `M`

## Output
* capsule enclosing `C` and `M * Cplus`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `enclose(C, M, Cplus)`: `C2 = M * Cplus`, then the hull of `C` and `C2`. -/
noncomputable def Capsule.enclose (C : Capsule n) (M : Mat ℝ n m) (Cplus : Capsule m) :
    Capsule n :=
  let C2 := Capsule.mtimes M Cplus
  C.convHull C2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
