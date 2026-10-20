import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.ContDynamics.NonlinearARX.Operations.ToNonlinearSysDTFloat
import CORALean.ContDynamics.NonlinearARX.Theorems.FloatModelEnclosesToNonlinearSysDTFloat
import CORALean.ContDynamics.NonlinearARX.Theorems.SimulateMemSimulateBoxFloat
import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.MulHi

/-!
# A nonlinear ARX model, simulated in boxes

The model `y(k) = y(k-1)/2 - y(k-2)²/4 + u(k)`, one output, one input and two lags. The square is
the nonlinearity: its interval extension at `Dyadic 24` is crude at a sign change but sound
(`model_encloses`). `NonlinearSysDT.simulateBoxFloat` is run on the converted system from the start
window `(y(0), y(1)) = (1, 1/2)` under the constant input `u = 1/16`, as
`NonlinearARX.simulateBoxFloat` does, and prints the box of each window. They are points: every
product here is exact at `Dyadic 24`. `NonlinearARX.simulate_mem_simulateBoxFloat` is the
guarantee: the real run of `f_ARX` has its stacked window, at every step, in the printed box.

## Inputs
* none

## Output
* nonlinear ARX example model
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.NonlinearARXFloat

open CORALean CORALean.Float FloatOps SoundFloatArithmetic

abbrev D := Dyadic 24

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

/-- A scalar read through `Float`, for printing. -/
def toF (x : D) : Float := Float.scaleB (Float.ofInt x.mantissa) x.exponent


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `y(k) = y(k-1)/2 - y(k-2)²/4 + u(k)`: the past outputs `(y(k-1), y(k-2))` and the inputs
`(u(k), u(k-1), u(k-2))`. -/
noncomputable def arxSys : NonlinearARX 1 1 2 where
  f y u := ![y 0 / 2 - y 1 ^ 2 / 4 + u 0]
  dt := 1

/-- The square's enclosure over `[a, b]`. -/
def sqLo (a b : D) : D := Interval.mulLo a b a b
def sqHi (a b : D) : D := Interval.mulHi a b a b

/-- An interval extension of `f_ARX`. -/
def model : NonlinearARX.FloatModel D 1 1 2 where
  f Y V :=
    ⟨![addDown (subDown (half (Y.inf 0)) (half (half (sqHi (Y.inf 1) (Y.sup 1))))) (V.inf 0)],
      ![addUp (subUp (half (Y.sup 0)) (half (half (sqLo (Y.inf 1) (Y.sup 1))))) (V.sup 0)]⟩

/-- The extension encloses `f_ARX` over every pair of boxes. -/
theorem model_encloses : model.Encloses arxSys := by -- --- PROOF ---
  -- the bounds on the arguments, and the roundings of each interval operation
  refine ⟨fun Y V y hy v hv => ?_⟩
  have hy0 : toReal (Y.inf 0) ≤ y 0 ∧ y 0 ≤ toReal (Y.sup 0) := hy 0
  have hy1 : toReal (Y.inf 1) ≤ y 1 ∧ y 1 ≤ toReal (Y.sup 1) := hy 1
  have hv0 : toReal (V.inf 0) ≤ v 0 ∧ v 0 ≤ toReal (V.sup 0) := hv 0
  obtain ⟨hl, hu⟩ := Interval.mul_between_corners hy1.1 hy1.2 hy1.1 hy1.2
  have r1 := addDown_le_add (subDown (half (Y.inf 0)) (half (half (sqHi (Y.inf 1) (Y.sup 1)))))
    (V.inf 0)
  have r2 := subDown_le_sub (half (Y.inf 0)) (half (half (sqHi (Y.inf 1) (Y.sup 1))))
  have r3 := add_le_addUp (subUp (half (Y.sup 0)) (half (half (sqLo (Y.inf 1) (Y.sup 1)))))
    (V.sup 0)
  have r4 := sub_le_subUp (half (Y.sup 0)) (half (half (sqLo (Y.inf 1) (Y.sup 1))))
  simp only [toReal_half] at r1 r2 r3 r4
  -- one coordinate, both faces
  intro i
  fin_cases i
  constructor
  · show toReal (addDown _ (V.inf 0)) ≤ y 0 / 2 - y 1 ^ 2 / 4 + v 0
    unfold sqHi at *
    nlinarith
  · show y 0 / 2 - y 1 ^ 2 / 4 + v 0 ≤ toReal (addUp _ (V.sup 0))
    unfold sqLo at *
    nlinarith

/-- The start window `(y(0), y(1)) = (1, 1/2)`: block `i` of a window holds `y(k+i)`. -/
def y₀ : Vec D 2 := ![d 1 0, d 1 (-1)]

/-- The constant input `1/16`. -/
def uIn : ℕ → Vec D 1 := fun _ => ![d 1 (-4)]

/-- The boxes of the stacked windows `(y(k), y(k+1))`, from the converted float model. -/
def boxes : ℕ → Interval (Vec D 2) :=
  NonlinearSysDT.simulateBoxFloat model.toNonlinearSysDTFloat y₀ (NonlinearARX.feed 2 uIn)

/-- `NonlinearARX.simulateBoxFloat` is that run (it ignores the real system). -/
theorem boxes_eq : arxSys.simulateBoxFloat model.toNonlinearSysDTFloat y₀ uIn = boxes := rfl

#eval (List.range 6).map fun k =>
  ((toF ((boxes k).inf 0), toF ((boxes k).sup 0)), (toF ((boxes k).inf 1), toF ((boxes k).sup 1)))

/-- The real run from `y₀` under `uIn` stays in the printed boxes. -/
theorem run_mem (k : ℕ) :
    NonlinearARX.stack 2
      (arxSys.simulate (Scalar.toRealVec y₀) fun j => Scalar.toRealVec (uIn j)) k ∈
      ContSet.construct (boxes k) :=
  NonlinearARX.simulate_mem_simulateBoxFloat arxSys model_encloses.toNonlinearSysDTFloat y₀ uIn k

end CORALean.Examples.NonlinearARXFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
