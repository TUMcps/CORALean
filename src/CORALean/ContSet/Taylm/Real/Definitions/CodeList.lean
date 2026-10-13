module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import CORALean.Global.Tensor

@[expose] public section

/-!
# Code lists

What [1, Thm. 2] and [1, Thm. 3] induct over: "a code list comprised of finitely many elementary
operations and intrinsic functions". `CodeList α m` is that list as a term over `m` input
variables with constants in `α` (`ℝ` here, a float type in the float layer); subtraction and
division are `add`/`neg` and `mul`/`inv`. `Intrinsic` names the intrinsics of the source's Def.
3 this tree has, the antiderivative excepted, which is not a function of a value; `eval` is the
real function a code list computes.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

/-- The intrinsic functions of the source's Def. 3 a code list may call. -/
inductive Taylm.Intrinsic
  | exp | log | inv | sqrt | invSqrt | sin | cos | sinh | cosh | asin | acos | atan | tan | tanh

/-- The real function an intrinsic denotes. -/
noncomputable def Taylm.Intrinsic.fn : Taylm.Intrinsic → ℝ → ℝ
  | .exp => Real.exp
  | .log => Real.log
  | .inv => fun x => x⁻¹
  | .sqrt => Real.sqrt
  | .invSqrt => fun x => (Real.sqrt x)⁻¹
  | .sin => Real.sin
  | .cos => Real.cos
  | .sinh => Real.sinh
  | .cosh => Real.cosh
  | .asin => Real.arcsin
  | .acos => Real.arccos
  | .atan => Real.arctan
  | .tan => Real.tan
  | .tanh => Real.tanh


-- ========================================  MAIN TYPE  ========================================= --

/-- A code list over `m` input variables with constants in `α`. -/
inductive Taylm.CodeList (α : Type) (m : ℕ) : Type
  | var (i : Fin m)
  | const (c : α)
  | add (a b : Taylm.CodeList α m)
  | mul (a b : Taylm.CodeList α m)
  | neg (a : Taylm.CodeList α m)
  | intr (s : Taylm.Intrinsic) (a : Taylm.CodeList α m)

/-- The real function a code list computes. -/
noncomputable def Taylm.CodeList.eval {m : ℕ} : Taylm.CodeList ℝ m → Vec ℝ m → ℝ
  | .var i, x => x i
  | .const c, _ => c
  | .add a b, x => a.eval x + b.eval x
  | .mul a b, x => a.eval x * b.eval x
  | .neg a, x => -a.eval x
  | .intr s a, x => s.fn (a.eval x)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
