module

public import CORALean.ContSet.Taylm.Float.Operations.Intrinsic
public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Operations.Times

@[expose] public section

/-!
# Executing a code list in floating-point Taylor model arithmetic

[1, Thm. 3]'s "the result obtained by executing the code list for `g` in admissible FP Taylor
model arithmetic": the exact layer's `codeEval` with each operation the float layer's, the
constants floats, and `p`, `q`, `s` the precisions of the float intrinsics. `none` when an
intrinsic's check fails or the float layer has no such intrinsic.

## Inputs
* `m` – number of variables
* `p` – precision of the exponential
* `q` – precision of the logarithm
* `s` – precision of the trigonometric functions
* `N` – expansion order
* `F` – variable models

## Output
* model of the code list's value, if all intrinsics are defined

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.codeEval {m : ℕ} (p q s N : ℕ) (F : Fin m → Taylm 𝕋 n) :
    Real.Taylm.CodeList 𝕋 m → Option (Taylm 𝕋 n)
  | .var i => some (F i)
  | .const c => some (Taylm.const n c N)
  | .add a b =>
    (Taylm.codeEval p q s N F a).bind fun A => (Taylm.codeEval p q s N F b).map A.plus
  | .mul a b =>
    (Taylm.codeEval p q s N F a).bind fun A => (Taylm.codeEval p q s N F b).map A.times
  | .neg a => (Taylm.codeEval p q s N F a).map Taylm.uminus
  | .intr k a => (Taylm.codeEval p q s N F a).bind (Taylm.intrinsic p q s k)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
