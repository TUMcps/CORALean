module

public import CORALean.ContSet.Taylm.Real.Operations.Asin
public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Operations.Minus

@[expose] public section

/-!
# `Taylm.acosPrinted`

[1, Def. 3 (arccos)] as printed: `arccos f = π/2 - arcsin f`, the constant model `π/2` minus
the model `Taylm.asin` gives of `arcsin f`. `Taylm.acos` is CORA's `acos`, which expands
`arccos` at the center directly; this is the source's own reduction to `arcsin`.

## Inputs
* `T` – Taylor model

## Output
* Taylor model of arccos as the paper prints it

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.acosPrinted (T : Taylm n) : Taylm n :=
  (Taylm.const n (Real.pi / 2) T.maxOrder).minus T.asin

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
