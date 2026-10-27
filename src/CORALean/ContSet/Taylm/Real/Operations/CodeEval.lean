module

public import CORALean.ContSet.Taylm.Real.Operations.Intrinsic
public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Operations.Plus
public import CORALean.ContSet.Taylm.Real.Operations.Times

@[expose] public section

/-!
# Executing a code list in Taylor model arithmetic

[1, Thm. 2]'s "the Taylor model obtained by executing the code list for `g`, beginning with the
Taylor model `P_f + I_f`": the input variables are the models `F`, a constant is a model of
order `N` with no remainder, and each operation is [1, Def. 2] or an intrinsic. `none` when an
intrinsic's condition fails on the model it is handed.

## Inputs
* `m` – number of variables
* `N` – expansion order
* `F` – variable models

## Output
* model of the code list's value, if all intrinsics are defined

## References

* [1] [K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics,
      2003.](../../../../../../references/2003/makino-ijpam-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.codeEval {m : ℕ} (N : ℕ) (F : Fin m → Taylm n) :
    Taylm.CodeList ℝ m → Option (Taylm n)
  | .var i => some (F i)
  | .const c => some (Taylm.const n c N)
  | .add a b => (Taylm.codeEval N F a).bind fun A => (Taylm.codeEval N F b).map A.plus
  | .mul a b => (Taylm.codeEval N F a).bind fun A => (Taylm.codeEval N F b).map A.times
  | .neg a => (Taylm.codeEval N F a).map Taylm.uminus
  | .intr s a => (Taylm.codeEval N F a).bind (Taylm.intrinsic s)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
