module

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
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcos
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcosh
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsin
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsinh
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtan
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtanh
public import CORALean.Specification.SyntaxTree.Operations.FunHanCos
public import CORALean.Specification.SyntaxTree.Operations.FunHanCosh
public import CORALean.Specification.SyntaxTree.Operations.FunHanExp
public import CORALean.Specification.SyntaxTree.Operations.FunHanLog
public import CORALean.Specification.SyntaxTree.Operations.FunHanMinus
public import CORALean.Specification.SyntaxTree.Operations.FunHanPlus
public import CORALean.Specification.SyntaxTree.Operations.FunHanPower
public import CORALean.Specification.SyntaxTree.Operations.FunHanSin
public import CORALean.Specification.SyntaxTree.Operations.FunHanSinh
public import CORALean.Specification.SyntaxTree.Operations.FunHanSqrt
public import CORALean.Specification.SyntaxTree.Operations.FunHanTan
public import CORALean.Specification.SyntaxTree.Operations.FunHanTanh
public import CORALean.Specification.SyntaxTree.Operations.FunHanTimes
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `SyntaxTree/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean
variable {n : ℕ}


-- ====================================  `SyntaxTree.acos`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `acos(obj)`: the node `'acos'` with `funHan = funHanAcos`. -/
noncomputable def SyntaxTree.acos (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .acos (Real.Interval.acos obj.value) funHanAcos obj


-- ====================================  `SyntaxTree.acosh`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `acosh(obj)`: the node `'acosh'` with `funHan = funHanAcosh`. -/
noncomputable def SyntaxTree.acosh (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .acosh (Real.Interval.acosh obj.value) funHanAcosh obj


-- ====================================  `SyntaxTree.asin`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `asin(obj)`: the node `'asin'` with `funHan = funHanAsin`. -/
noncomputable def SyntaxTree.asin (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .asin (Real.Interval.asin obj.value) funHanAsin obj


-- ====================================  `SyntaxTree.asinh`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `asinh(obj)`: the node `'asinh'` with `funHan = funHanAsinh`. -/
noncomputable def SyntaxTree.asinh (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .asinh (Real.Interval.asinh obj.value) funHanAsinh obj


-- ====================================  `SyntaxTree.atan`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `atan(obj)`: the node `'atan'` with `funHan = funHanAtan`. -/
noncomputable def SyntaxTree.atan (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .atan (Real.Interval.atan obj.value) funHanAtan obj


-- ====================================  `SyntaxTree.atanh`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `atanh(obj)`: the node `'atanh'` with `funHan = funHanAtanh`. -/
noncomputable def SyntaxTree.atanh (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .atanh (Real.Interval.atanh obj.value) funHanAtanh obj


-- =====================================  `SyntaxTree.cos`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `cos(obj)`: the node `'cos'` with `funHan = funHanCos`. -/
noncomputable def SyntaxTree.cos (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .cos (Real.Interval.cos obj.value) funHanCos obj


-- ====================================  `SyntaxTree.cosh`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `cosh(obj)`: the node `'cosh'` with `funHan = funHanCosh`. -/
noncomputable def SyntaxTree.cosh (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .cosh (Real.Interval.cosh obj.value) funHanCosh obj


-- =====================================  `SyntaxTree.exp`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `exp(obj)`: the node `'exp'` with `funHan = funHanExp`. -/
noncomputable def SyntaxTree.exp (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .exp (Real.Interval.exp obj.value) funHanExp obj


-- ================================  `SyntaxTree.funHanUminus`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `aux_uminus_`: `-int & intPrev`. -/
noncomputable def SyntaxTree.funHanUminus (int prev : Dom) : Outcome Dom :=
  .ok (Real.Interval.intersection (Real.Interval.uminus int) prev)


-- =====================================  `SyntaxTree.log`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `log(obj)`: the node `'log'` with `funHan = funHanLog`. -/
noncomputable def SyntaxTree.log (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .log (Real.Interval.log obj.value) funHanLog obj


-- ====================================  `SyntaxTree.minus`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus(obj1,obj2)` of two trees: the node `'-'` with `funHan = funHanMinus`. -/
noncomputable def SyntaxTree.minus (obj₁ obj₂ : SyntaxTree n) : SyntaxTree n :=
  .binary .minus (Real.Interval.minus obj₁.value obj₂.value) funHanMinus obj₁ obj₂


-- ================================  `SyntaxTree.minusNumLeft`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus(c,obj2)` with a number first: the node `'-'`, the number a numeric operand. -/
noncomputable def SyntaxTree.minusNumLeft (c : ℝ) (obj₂ : SyntaxTree n) : SyntaxTree n :=
  .numLeft .minus (Real.Interval.minus (interval c c) obj₂.value) funHanMinus c
    obj₂


-- ================================  `SyntaxTree.minusNumRight`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus(obj1,c)` with a number second: the node `'-'`, the number a numeric operand. -/
noncomputable def SyntaxTree.minusNumRight (obj₁ : SyntaxTree n) (c : ℝ) : SyntaxTree n :=
  .numRight .minus (Real.Interval.minus obj₁.value (interval c c)) funHanMinus
    obj₁ c


-- ===================================  `SyntaxTree.mpower`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `mpower(obj,exp)`: derived from `power`, the same node for a scalar. -/
noncomputable def SyntaxTree.mpower (obj : SyntaxTree n) (k : ℕ) : SyntaxTree n :=
  .unary (.power k) (Real.Interval.power obj.value k) (funHanPower k) obj


-- ====================================  `SyntaxTree.plus`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus(obj1,obj2)` of two trees: the node `'+'` with `funHan = funHanPlus`. -/
noncomputable def SyntaxTree.plus (obj₁ obj₂ : SyntaxTree n) : SyntaxTree n :=
  .binary .plus (Real.Interval.plus obj₁.value obj₂.value) funHanPlus obj₁ obj₂


-- =================================  `SyntaxTree.plusNumLeft`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus(c,obj2)` with a number first: the node `'+'`, the number a numeric operand. -/
noncomputable def SyntaxTree.plusNumLeft (c : ℝ) (obj₂ : SyntaxTree n) : SyntaxTree n :=
  .numLeft .plus (Real.Interval.plus (interval c c) obj₂.value) funHanPlus c obj₂


-- ================================  `SyntaxTree.plusNumRight`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus(obj1,c)` with a number second: the node `'+'`, the number a numeric operand. -/
noncomputable def SyntaxTree.plusNumRight (obj₁ : SyntaxTree n) (c : ℝ) : SyntaxTree n :=
  .numRight .plus (Real.Interval.plus obj₁.value (interval c c)) funHanPlus obj₁ c


-- ====================================  `SyntaxTree.power`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `power(obj,exp)`: the node `'power'`, `value = obj.value^exp`, `funHan = funHanPower` (a
natural exponent). -/
noncomputable def SyntaxTree.power (obj : SyntaxTree n) (k : ℕ) : SyntaxTree n :=
  .unary (.power k) (Real.Interval.power obj.value k) (funHanPower k) obj


-- =====================================  `SyntaxTree.sin`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sin(obj)`: the node `'sin'` with `funHan = funHanSin`. -/
noncomputable def SyntaxTree.sin (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .sin (Real.Interval.sin obj.value) funHanSin obj


-- ====================================  `SyntaxTree.sinh`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sinh(obj)`: the node `'sinh'` with the corrected `aux_sinh_`, as `aux_sinhCora_` is unsound. -/
noncomputable def SyntaxTree.sinh (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .sinh (Real.Interval.sinh obj.value) funHanSinh obj


-- ====================================  `SyntaxTree.sqrt`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sqrt(obj)`: the node `'sqrt'` with `funHan = funHanSqrt`. -/
noncomputable def SyntaxTree.sqrt (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .sqrt (Real.Interval.sqrt obj.value) funHanSqrt obj


-- =====================================  `SyntaxTree.sum`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sum(obj)` of a vector of trees: the first entry, then `res + obj(i)`. -/
noncomputable def SyntaxTree.sum (obj : SyntaxTree n) (rest : List (SyntaxTree n)) : SyntaxTree n :=
  rest.foldl SyntaxTree.plus obj


-- =====================================  `SyntaxTree.tan`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `tan(obj)`: the node `'tan'` with the corrected `aux_tan_`, as `aux_tanCora_` is unsound. -/
noncomputable def SyntaxTree.tan (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .tan (Real.Interval.tan obj.value) funHanTan obj


-- ====================================  `SyntaxTree.tanh`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `tanh(obj)`: the node `'tanh'` with `funHan = funHanTanh`. -/
noncomputable def SyntaxTree.tanh (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .tanh (Real.Interval.tanh obj.value) funHanTanh obj


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

/-- `prod(obj)` of a vector of trees: the first entry, then `res .* obj(i)`. -/
noncomputable def SyntaxTree.prod (obj : SyntaxTree n) (rest : List (SyntaxTree n)) : SyntaxTree n
    :=
  rest.foldl SyntaxTree.times obj


-- ================================  `SyntaxTree.timesNumLeft`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `times(c,obj2)` with a number first: the node `'*'`, the number a numeric operand. -/
noncomputable def SyntaxTree.timesNumLeft (c : ℝ) (obj₂ : SyntaxTree n) : SyntaxTree n :=
  .numLeft .times (Real.Interval.times (interval c c) obj₂.value) funHanTimes c
    obj₂


-- ================================  `SyntaxTree.timesNumRight`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `times(obj1,c)` with a number second: the node `'*'`, the number a numeric operand. -/
noncomputable def SyntaxTree.timesNumRight (obj₁ : SyntaxTree n) (c : ℝ) : SyntaxTree n :=
  .numRight .times (Real.Interval.times obj₁.value (interval c c)) funHanTimes
    obj₁ c


-- ===================================  `SyntaxTree.uminus`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `uminus(obj)`: the node `'uminus'` with `funHan = funHanUminus`. -/
noncomputable def SyntaxTree.uminus (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .uminus (Real.Interval.uminus obj.value) SyntaxTree.funHanUminus obj


-- ====================================  `SyntaxTree.uplus`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `uplus(obj)`: the tree itself. -/
def SyntaxTree.uplus (obj : SyntaxTree n) : SyntaxTree n := obj


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
