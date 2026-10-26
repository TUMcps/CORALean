module

public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Float.Operations.Acos
public import CORALean.ContSet.Interval.Float.Operations.Acosh
public import CORALean.ContSet.Interval.Float.Operations.Asin
public import CORALean.ContSet.Interval.Float.Operations.Asinh
public import CORALean.ContSet.Interval.Float.Operations.Atan
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Cos
public import CORALean.ContSet.Interval.Float.Operations.Log
public import CORALean.ContSet.Interval.Float.Operations.Power
public import CORALean.ContSet.Interval.Float.Operations.Sin
public import CORALean.ContSet.Interval.Float.Operations.Sqrt
public import CORALean.ContSet.Interval.Float.Operations.Tan
public import CORALean.ContSet.Interval.Float.Operations.Times
public import CORALean.ContSet.Interval.Real.Operations.Acosh
public import CORALean.ContSet.Interval.Real.Operations.Asinh
public import CORALean.ContSet.Interval.Real.Operations.Atan
public import CORALean.ContSet.Interval.Real.Operations.Atanh
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Cos
public import CORALean.ContSet.Interval.Real.Operations.Exp
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.ContSet.Interval.Real.Operations.Power
public import CORALean.ContSet.Interval.Real.Operations.Sinh
public import CORALean.ContSet.Interval.Real.Operations.Sqrt
public import CORALean.ContSet.Interval.Real.Operations.Tan
public import CORALean.ContSet.Interval.Real.Operations.Times
public import CORALean.Specification.SyntaxTree.Definitions.SyntaxTreeFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcos
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcosFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcosh
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcoshFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsin
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsinFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsinh
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsinhFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtan
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtanFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtanh
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtanhFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanCos
public import CORALean.Specification.SyntaxTree.Operations.FunHanCosFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanCosh
public import CORALean.Specification.SyntaxTree.Operations.FunHanCoshFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanExp
public import CORALean.Specification.SyntaxTree.Operations.FunHanExpFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanLog
public import CORALean.Specification.SyntaxTree.Operations.FunHanLogFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanMinus
public import CORALean.Specification.SyntaxTree.Operations.FunHanMinusFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanPlus
public import CORALean.Specification.SyntaxTree.Operations.FunHanPlusFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanPower
public import CORALean.Specification.SyntaxTree.Operations.FunHanPowerFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanSin
public import CORALean.Specification.SyntaxTree.Operations.FunHanSinFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanSinh
public import CORALean.Specification.SyntaxTree.Operations.FunHanSinhFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanSqrt
public import CORALean.Specification.SyntaxTree.Operations.FunHanSqrtFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanTan
public import CORALean.Specification.SyntaxTree.Operations.FunHanTanFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanTanh
public import CORALean.Specification.SyntaxTree.Operations.FunHanTanhFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanTimes
public import CORALean.Specification.SyntaxTree.Operations.FunHanTimesFloat
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat
public import CORALean.Specification.SyntaxTree.Operations.ValueFloat
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `SyntaxTree/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the sections each one
uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean
variable {n : ℕ}
variable {𝕋 : Type} [Float.FloatOps 𝕋]


-- ====================================  `SyntaxTree.acos`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `acos(obj)`: the node `'acos'` with `funHan = funHanAcos`. -/
noncomputable def SyntaxTree.acos (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .acos (Real.Interval.acos obj.value) funHanAcos obj


-- ==================================  `SyntaxTree.acosFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `acos(obj)` over floats: the node `'acos'` with `funHan = funHanAcosFloat`. -/
def SyntaxTree.acosFloat (p k : ℕ) (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .acos (Float.Interval.acos p k obj.value) (SyntaxTree.funHanAcosFloat p) obj


-- ====================================  `SyntaxTree.acosh`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `acosh(obj)`: the node `'acosh'` with `funHan = funHanAcosh`. -/
noncomputable def SyntaxTree.acosh (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .acosh (Real.Interval.acosh obj.value) funHanAcosh obj


-- =================================  `SyntaxTree.acoshFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `acosh(obj)` over floats: the node `'acosh'` with `funHan = funHanAcoshFloat`. -/
def SyntaxTree.acoshFloat (p k : ℕ) (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .acosh (Float.Interval.acosh p k obj.value) (SyntaxTree.funHanAcoshFloat p) obj


-- ====================================  `SyntaxTree.asin`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `asin(obj)`: the node `'asin'` with `funHan = funHanAsin`. -/
noncomputable def SyntaxTree.asin (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .asin (Real.Interval.asin obj.value) funHanAsin obj


-- ==================================  `SyntaxTree.asinFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `asin(obj)` over floats: the node `'asin'` with `funHan = funHanAsinFloat`. -/
def SyntaxTree.asinFloat (p k : ℕ) (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .asin (Float.Interval.asin p k obj.value) (SyntaxTree.funHanAsinFloat p k) obj


-- ====================================  `SyntaxTree.asinh`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `asinh(obj)`: the node `'asinh'` with `funHan = funHanAsinh`. -/
noncomputable def SyntaxTree.asinh (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .asinh (Real.Interval.asinh obj.value) funHanAsinh obj


-- =================================  `SyntaxTree.asinhFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `asinh(obj)` over floats: the node `'asinh'` with `funHan = funHanAsinhFloat`. -/
def SyntaxTree.asinhFloat (p k : ℕ) (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .asinh (Float.Interval.asinh p k obj.value) (SyntaxTree.funHanAsinhFloat p) obj


-- ====================================  `SyntaxTree.atan`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `atan(obj)`: the node `'atan'` with `funHan = funHanAtan`. -/
noncomputable def SyntaxTree.atan (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .atan (Real.Interval.atan obj.value) funHanAtan obj


-- ==================================  `SyntaxTree.atanFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `atan(obj)` over floats: the node `'atan'` with `funHan = funHanAtanFloat`. -/
def SyntaxTree.atanFloat (p k : ℕ) (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .atan (Float.Interval.atan p k obj.value) (SyntaxTree.funHanAtanFloat p k) obj


-- ====================================  `SyntaxTree.atanh`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)

/-- `atanh(obj)`: the node `'atanh'` with `funHan = funHanAtanh`. -/
noncomputable def SyntaxTree.atanh (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .atanh (Real.Interval.atanh obj.value) funHanAtanh obj


-- =================================  `SyntaxTree.atanhFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `atanh(obj)` over floats: the node `'atanh'` with `funHan = funHanAtanhFloat`. -/
def SyntaxTree.atanhFloat (p k : ℕ) (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .atanh (Float.Interval.atanh p k obj.value) (SyntaxTree.funHanAtanhFloat p) obj


-- =====================================  `SyntaxTree.cos`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `cos(obj)`: the node `'cos'` with `funHan = funHanCos`. -/
noncomputable def SyntaxTree.cos (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .cos (Real.Interval.cos obj.value) funHanCos obj


-- ==================================  `SyntaxTree.cosFloat`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `cos(obj)` over floats: the node `'cos'` with `funHan = funHanCosFloat`. -/
def SyntaxTree.cosFloat [Float.SoundFloatArithmetic 𝕋] [Float.ToRat 𝕋] (p k : ℕ)
    (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .cos (Float.Interval.cos p obj.value) (SyntaxTree.funHanCosFloat p k) obj


-- ====================================  `SyntaxTree.cosh`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `cosh(obj)`: the node `'cosh'` with `funHan = funHanCosh`. -/
noncomputable def SyntaxTree.cosh (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .cosh (Real.Interval.cosh obj.value) funHanCosh obj


-- ==================================  `SyntaxTree.coshFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `cosh(obj)` over floats: the node `'cosh'` with `funHan = funHanCoshFloat`. -/
def SyntaxTree.coshFloat (p k : ℕ) (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .cosh (Float.Interval.cosh p obj.value) (SyntaxTree.funHanCoshFloat p k) obj


-- =====================================  `SyntaxTree.exp`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `exp(obj)`: the node `'exp'` with `funHan = funHanExp`. -/
noncomputable def SyntaxTree.exp (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .exp (Real.Interval.exp obj.value) funHanExp obj


-- ==================================  `SyntaxTree.expFloat`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `exp(obj)` over floats: the node `'exp'` with `funHan = funHanExpFloat`. -/
def SyntaxTree.expFloat (p k : ℕ) (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .exp (Float.Interval.exp p obj.value) (SyntaxTree.funHanExpFloat p k) obj


-- ================================  `SyntaxTree.funHanUminus`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `aux_uminus_`: `-int & intPrev`. -/
noncomputable def SyntaxTree.funHanUminus (int prev : Dom) : Outcome Dom :=
  .ok (Real.Interval.intersection (Real.Interval.uminus int) prev)


-- ==============================  `SyntaxTree.funHanUminusFloat`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `aux_uminus_` over floats: `-int & intPrev`. -/
def SyntaxTree.funHanUminusFloat (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  .ok (Float.Interval.intersection (Float.Interval.uminus int) prev)


-- =====================================  `SyntaxTree.log`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `log(obj)`: the node `'log'` with `funHan = funHanLog`. -/
noncomputable def SyntaxTree.log (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .log (Real.Interval.log obj.value) funHanLog obj


-- ==================================  `SyntaxTree.logFloat`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `log(obj)` over floats: the node `'log'` with `funHan = funHanLogFloat`. -/
def SyntaxTree.logFloat (p k : ℕ) (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .log (Float.Interval.log p k obj.value) (SyntaxTree.funHanLogFloat p) obj


-- ====================================  `SyntaxTree.minus`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus(obj1,obj2)` of two trees: the node `'-'` with `funHan = funHanMinus`. -/
noncomputable def SyntaxTree.minus (obj₁ obj₂ : SyntaxTree n) : SyntaxTree n :=
  .binary .minus (Real.Interval.minus obj₁.value obj₂.value) funHanMinus obj₁ obj₂


-- =================================  `SyntaxTree.minusFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus(obj1,obj2)` of two trees over floats: the node `'-'`. -/
def SyntaxTree.minusFloat (obj₁ obj₂ : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .binary .minus (Float.Interval.minus obj₁.value obj₂.value) SyntaxTree.funHanMinusFloat obj₁ obj₂


-- ================================  `SyntaxTree.minusNumLeft`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus(c,obj2)` with a number first: the node `'-'`, the number a numeric operand. -/
noncomputable def SyntaxTree.minusNumLeft (c : ℝ) (obj₂ : SyntaxTree n) : SyntaxTree n :=
  .numLeft .minus (Real.Interval.minus (interval c c) obj₂.value) funHanMinus c
    obj₂


-- ==============================  `SyntaxTree.minusNumLeftFloat`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus(c,obj2)` over floats, a number first: the node `'-'`. -/
def SyntaxTree.minusNumLeftFloat (c : 𝕋) (obj₂ : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .numLeft .minus (Float.Interval.minus (SyntaxTree.intervalFloat c c) obj₂.value)
    SyntaxTree.funHanMinusFloat c obj₂


-- ================================  `SyntaxTree.minusNumRight`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus(obj1,c)` with a number second: the node `'-'`, the number a numeric operand. -/
noncomputable def SyntaxTree.minusNumRight (obj₁ : SyntaxTree n) (c : ℝ) : SyntaxTree n :=
  .numRight .minus (Real.Interval.minus obj₁.value (interval c c)) funHanMinus
    obj₁ c


-- =============================  `SyntaxTree.minusNumRightFloat`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus(obj1,c)` over floats, a number second: the node `'-'`. -/
def SyntaxTree.minusNumRightFloat (obj₁ : Float.SyntaxTree 𝕋 n) (c : 𝕋) : Float.SyntaxTree 𝕋 n :=
  .numRight .minus (Float.Interval.minus obj₁.value (SyntaxTree.intervalFloat c c))
    SyntaxTree.funHanMinusFloat obj₁ c


-- ===================================  `SyntaxTree.mpower`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `mpower(obj,exp)`: derived from `power`, the same node for a scalar. -/
noncomputable def SyntaxTree.mpower (obj : SyntaxTree n) (k : ℕ) : SyntaxTree n :=
  .unary (.power k) (Real.Interval.power obj.value k) (funHanPower k) obj


-- =================================  `SyntaxTree.mpowerFloat`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `mpower(obj,exp)` over floats: derived from `power`, the same node for a scalar. -/
def SyntaxTree.mpowerFloat (steps k : ℕ) (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary (.power k) (Float.Interval.power obj.value k) (SyntaxTree.funHanPowerFloat steps k) obj


-- ====================================  `SyntaxTree.plus`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus(obj1,obj2)` of two trees: the node `'+'` with `funHan = funHanPlus`. -/
noncomputable def SyntaxTree.plus (obj₁ obj₂ : SyntaxTree n) : SyntaxTree n :=
  .binary .plus (Real.Interval.plus obj₁.value obj₂.value) funHanPlus obj₁ obj₂


-- ==================================  `SyntaxTree.plusFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus(obj1,obj2)` of two trees over floats: the node `'+'`. -/
def SyntaxTree.plusFloat (obj₁ obj₂ : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .binary .plus (Float.Interval.plus obj₁.value obj₂.value) SyntaxTree.funHanPlusFloat obj₁ obj₂


-- =================================  `SyntaxTree.plusNumLeft`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus(c,obj2)` with a number first: the node `'+'`, the number a numeric operand. -/
noncomputable def SyntaxTree.plusNumLeft (c : ℝ) (obj₂ : SyntaxTree n) : SyntaxTree n :=
  .numLeft .plus (Real.Interval.plus (interval c c) obj₂.value) funHanPlus c obj₂


-- ==============================  `SyntaxTree.plusNumLeftFloat`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus(c,obj2)` over floats, a number first: the node `'+'`. -/
def SyntaxTree.plusNumLeftFloat (c : 𝕋) (obj₂ : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .numLeft .plus (Float.Interval.plus (SyntaxTree.intervalFloat c c) obj₂.value)
    SyntaxTree.funHanPlusFloat c obj₂


-- ================================  `SyntaxTree.plusNumRight`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus(obj1,c)` with a number second: the node `'+'`, the number a numeric operand. -/
noncomputable def SyntaxTree.plusNumRight (obj₁ : SyntaxTree n) (c : ℝ) : SyntaxTree n :=
  .numRight .plus (Real.Interval.plus obj₁.value (interval c c)) funHanPlus obj₁ c


-- ==============================  `SyntaxTree.plusNumRightFloat`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus(obj1,c)` over floats, a number second: the node `'+'`. -/
def SyntaxTree.plusNumRightFloat (obj₁ : Float.SyntaxTree 𝕋 n) (c : 𝕋) : Float.SyntaxTree 𝕋 n :=
  .numRight .plus (Float.Interval.plus obj₁.value (SyntaxTree.intervalFloat c c))
    SyntaxTree.funHanPlusFloat obj₁ c


-- ====================================  `SyntaxTree.power`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `power(obj,exp)`: the node `'power'`, `value = obj.value^exp`, `funHan = funHanPower` (a
natural exponent). -/
noncomputable def SyntaxTree.power (obj : SyntaxTree n) (k : ℕ) : SyntaxTree n :=
  .unary (.power k) (Real.Interval.power obj.value k) (funHanPower k) obj


-- =================================  `SyntaxTree.powerFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `power(obj,exp)` over floats: the node `'power'`, a natural exponent. -/
def SyntaxTree.powerFloat (steps k : ℕ) (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary (.power k) (Float.Interval.power obj.value k) (SyntaxTree.funHanPowerFloat steps k) obj


-- =====================================  `SyntaxTree.sin`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sin(obj)`: the node `'sin'` with `funHan = funHanSin`. -/
noncomputable def SyntaxTree.sin (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .sin (Real.Interval.sin obj.value) funHanSin obj


-- ==================================  `SyntaxTree.sinFloat`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sin(obj)` over floats: the node `'sin'` with `funHan = funHanSinFloat`. -/
def SyntaxTree.sinFloat [Float.SoundFloatArithmetic 𝕋] [Float.ToRat 𝕋] (p k : ℕ)
    (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .sin (Float.Interval.sin p obj.value) (SyntaxTree.funHanSinFloat p k) obj


-- ====================================  `SyntaxTree.sinh`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sinh(obj)`: the node `'sinh'` with the corrected `aux_sinh_`, as `aux_sinhCora_` is unsound. -/
noncomputable def SyntaxTree.sinh (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .sinh (Real.Interval.sinh obj.value) funHanSinh obj


-- ==================================  `SyntaxTree.sinhFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sinh(obj)` over floats: the node `'sinh'` with `funHan = funHanSinhFloat`. -/
def SyntaxTree.sinhFloat (p k : ℕ) (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .sinh (Float.Interval.sinh p obj.value) (SyntaxTree.funHanSinhFloat p k) obj


-- ====================================  `SyntaxTree.sqrt`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sqrt(obj)`: the node `'sqrt'` with `funHan = funHanSqrt`. -/
noncomputable def SyntaxTree.sqrt (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .sqrt (Real.Interval.sqrt obj.value) funHanSqrt obj


-- ==================================  `SyntaxTree.sqrtFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sqrt(obj)` over floats: the node `'sqrt'` with `funHan = funHanSqrtFloat`. -/
def SyntaxTree.sqrtFloat (p : ℕ) (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .sqrt (Float.Interval.sqrt p obj.value) (SyntaxTree.funHanSqrtFloat) obj


-- =====================================  `SyntaxTree.sum`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sum(obj)` of a vector of trees: the first entry, then `res + obj(i)`. Noncomputable because
`plus` is. -/
noncomputable def SyntaxTree.sum (obj : SyntaxTree n) (rest : List (SyntaxTree n)) : SyntaxTree n :=
  rest.foldl SyntaxTree.plus obj


-- ==================================  `SyntaxTree.sumFloat`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sum(obj)` of a vector of trees over floats: the first entry, then `res + obj(i)`. -/
def SyntaxTree.sumFloat (obj : Float.SyntaxTree 𝕋 n) (rest : List (Float.SyntaxTree 𝕋 n)) :
    Float.SyntaxTree 𝕋 n :=
  rest.foldl SyntaxTree.plusFloat obj


-- =====================================  `SyntaxTree.tan`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `tan(obj)`: the node `'tan'` with the corrected `aux_tan_`, as `aux_tanCora_` is unsound. -/
noncomputable def SyntaxTree.tan (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .tan (Real.Interval.tan obj.value) funHanTan obj


-- ==================================  `SyntaxTree.tanFloat`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `tan(obj)` over floats: the node `'tan'` with `funHan = funHanTanFloat`. -/
def SyntaxTree.tanFloat [Float.SoundFloatArithmetic 𝕋] [Float.ToRat 𝕋] (p k : ℕ)
    (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .tan (Float.Interval.tan p obj.value) (SyntaxTree.funHanTanFloat p k) obj


-- ====================================  `SyntaxTree.tanh`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `tanh(obj)`: the node `'tanh'` with `funHan = funHanTanh`. -/
noncomputable def SyntaxTree.tanh (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .tanh (Real.Interval.tanh obj.value) funHanTanh obj


-- ==================================  `SyntaxTree.tanhFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `tanh(obj)` over floats: the node `'tanh'` with `funHan = funHanTanhFloat`. -/
def SyntaxTree.tanhFloat (p k : ℕ) (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .tanh (Float.Interval.tanh p obj.value) (SyntaxTree.funHanTanhFloat p k) obj


-- ====================================  `SyntaxTree.times`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `times(obj1,obj2)` of two trees: the node `'*'` with `funHan = funHanTimes`. -/
noncomputable def SyntaxTree.times (obj₁ obj₂ : SyntaxTree n) : SyntaxTree n :=
  .binary .times (Real.Interval.times obj₁.value obj₂.value) funHanTimes obj₁ obj₂


-- ====================================  `SyntaxTree.prod`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `prod(obj)` of a vector of trees: the first entry, then `res .* obj(i)`. Noncomputable because
`times` is. -/
noncomputable def SyntaxTree.prod (obj : SyntaxTree n) (rest : List (SyntaxTree n)) : SyntaxTree n
    :=
  rest.foldl SyntaxTree.times obj


-- =================================  `SyntaxTree.timesFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `times(obj1,obj2)` of two trees over floats: the node `'*'`. -/
def SyntaxTree.timesFloat (obj₁ obj₂ : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .binary .times (Float.Interval.times obj₁.value obj₂.value) SyntaxTree.funHanTimesFloat obj₁ obj₂


-- ==================================  `SyntaxTree.prodFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `prod(obj)` of a vector of trees over floats: the first entry, then `res .* obj(i)`. -/
def SyntaxTree.prodFloat (obj : Float.SyntaxTree 𝕋 n) (rest : List (Float.SyntaxTree 𝕋 n)) :
    Float.SyntaxTree 𝕋 n :=
  rest.foldl SyntaxTree.timesFloat obj


-- ================================  `SyntaxTree.timesNumLeft`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `times(c,obj2)` with a number first: the node `'*'`, the number a numeric operand. -/
noncomputable def SyntaxTree.timesNumLeft (c : ℝ) (obj₂ : SyntaxTree n) : SyntaxTree n :=
  .numLeft .times (Real.Interval.times (interval c c) obj₂.value) funHanTimes c
    obj₂


-- ==============================  `SyntaxTree.timesNumLeftFloat`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `times(c,obj2)` over floats, a number first: the node `'*'`. -/
def SyntaxTree.timesNumLeftFloat (c : 𝕋) (obj₂ : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .numLeft .times (Float.Interval.times (SyntaxTree.intervalFloat c c) obj₂.value)
    SyntaxTree.funHanTimesFloat c obj₂


-- ================================  `SyntaxTree.timesNumRight`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `times(obj1,c)` with a number second: the node `'*'`, the number a numeric operand. -/
noncomputable def SyntaxTree.timesNumRight (obj₁ : SyntaxTree n) (c : ℝ) : SyntaxTree n :=
  .numRight .times (Real.Interval.times obj₁.value (interval c c)) funHanTimes
    obj₁ c


-- =============================  `SyntaxTree.timesNumRightFloat`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `times(obj1,c)` over floats, a number second: the node `'*'`. -/
def SyntaxTree.timesNumRightFloat (obj₁ : Float.SyntaxTree 𝕋 n) (c : 𝕋) : Float.SyntaxTree 𝕋 n :=
  .numRight .times (Float.Interval.times obj₁.value (SyntaxTree.intervalFloat c c))
    SyntaxTree.funHanTimesFloat obj₁ c


-- ===================================  `SyntaxTree.uminus`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `uminus(obj)`: the node `'uminus'` with `funHan = funHanUminus`. -/
noncomputable def SyntaxTree.uminus (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .uminus (Real.Interval.uminus obj.value) SyntaxTree.funHanUminus obj


-- =================================  `SyntaxTree.uminusFloat`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `uminus(obj)` over floats: the node `'uminus'` with `funHan = funHanUminusFloat`. -/
def SyntaxTree.uminusFloat (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n :=
  .unary .uminus (Float.Interval.uminus obj.value) (SyntaxTree.funHanUminusFloat) obj


-- ====================================  `SyntaxTree.uplus`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `uplus(obj)`: the tree itself. -/
def SyntaxTree.uplus (obj : SyntaxTree n) : SyntaxTree n := obj


-- =================================  `SyntaxTree.uplusFloat`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `uplus(obj)` over floats: the tree itself. -/
def SyntaxTree.uplusFloat (obj : Float.SyntaxTree 𝕋 n) : Float.SyntaxTree 𝕋 n := obj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
