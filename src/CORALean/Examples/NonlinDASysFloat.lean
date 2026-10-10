import CORALean.ContDynamics.NonlinDASys.API
import CORALean.ContDynamics.NonlinDASys.Operations.ReachFloatChecked
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachFloatOuter
import CORALean.Global.Float.Instances.Dyadic.API
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# A differential-algebraic system, run in floats

The system `ẋ = -x + y`, `0 = y - x/2 - u`, one state, one algebraic variable and one input. The
constraint is solved by `y = x/2 + u` (`ReducedModel`, with its uniqueness), which leaves the
ordinary system `ẋ = -x/2 + u`. `NonlinDASys.reachFloat` runs that system at `Dyadic 24` from the
box `x ∈ [3/4, 5/4]` under `u ∈ [-1/16, 1/16]` for one time unit in steps of `1/8`, from an
interval model of the reduced field and its slopes (proved to enclose it, below), and prints the
range of each window.

`NonlinDASys.reachFloat_outer` is the guarantee, applied here to this system: whenever the run
returns `some Rs`, the differential variable of every trajectory of the algebraic system from the
box, under inputs in the interval, lies at every time of window `k` in `Rs[k]`. The `#eval`
shows the run returns `some` (eight windows).
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.NonlinDASysFloat

open CORALean CORALean.Float FloatOps SoundFloatArithmetic

abbrev D := Dyadic 24

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

/-- Zero width in every coordinate. -/
def zbox (n : ℕ) : Interval (Vec D n) := ⟨fun _ => d 0 0, fun _ => d 0 0⟩

/-- A scalar read through `Float`, for printing. -/
def toF (x : D) : Float := Float.scaleB (Float.ofInt x.mantissa) x.exponent


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ẋ = -x + y`, `0 = y - x/2 - u`. -/
noncomputable def daeSys : NonlinDASys 1 1 1 where
  f x y _ := ![-x 0 + y 0]
  g x y u := ![y 0 - x 0 / 2 - u 0]

/-- The constraint solved for `y`, and the only solution. -/
noncomputable def daeRed : daeSys.ReducedModel where
  h x u := ![x 0 / 2 + u 0]
  sound x u := by ext i; fin_cases i; simp [daeSys]
  unique x y u hg := by
    ext i; fin_cases i
    have := congrFun hg 0
    simp [daeSys] at this ⊢
    linarith

/-- Interval extensions of the reduced field `-x/2 + u` and of its slopes `-1/2` and `1`. -/
def model : NonlinearSys.FloatModel D 1 1 where
  f X U :=
    ⟨![addDown (U.inf 0) (neg (half (X.sup 0)))], ![addUp (U.sup 0) (neg (half (X.inf 0)))]⟩
  jacX _ _ := ⟨!![neg (half one)], !![neg (half one)]⟩
  jacU _ _ := ⟨!![one], !![one]⟩

/-- The model encloses the reduced system, over every box. -/
theorem model_encloses : model.Encloses daeRed.toNonlinearSys := by -- --- PROOF ---
  -- the field's value, then the slopes
  refine ⟨fun X U x hx u hu => ?_, fun X U x hx x' hx' u hu u' hu' => ?_⟩
  · have hx0 : toReal (X.inf 0) ≤ x 0 ∧ x 0 ≤ toReal (X.sup 0) := hx 0
    have hu0 : toReal (U.inf 0) ≤ u 0 ∧ u 0 ≤ toReal (U.sup 0) := hu 0
    have r1 := addDown_le_add (U.inf 0) (neg (half (X.sup 0)))
    have r2 := add_le_addUp (U.sup 0) (neg (half (X.inf 0)))
    rw [toReal_neg, toReal_half] at r1 r2
    -- one coordinate, both faces: one rounding per operation, each the safe way
    intro i
    fin_cases i
    constructor
    · show toReal (addDown (U.inf 0) (neg (half (X.sup 0)))) ≤ -x 0 + (x 0 / 2 + u 0)
      linarith
    · show -x 0 + (x 0 / 2 + u 0) ≤ toReal (addUp (U.sup 0) (neg (half (X.inf 0))))
      linarith
  -- the slopes are the constants `-1/2` and `1`, exact in the boxes
  · refine ⟨!![-1 / 2], fun q => ?_, !![1], fun q => ?_, ?_⟩
    · obtain ⟨i, j⟩ := q
      fin_cases i; fin_cases j
      show toReal (neg (half (one : D))) ≤ -1 / 2 ∧ -1 / 2 ≤ toReal (neg (half (one : D)))
      rw [toReal_neg, toReal_half, toReal_one]
      constructor <;> norm_num
    · obtain ⟨i, j⟩ := q
      fin_cases i; fin_cases j
      show toReal (one : D) ≤ 1 ∧ 1 ≤ toReal (one : D)
      rw [toReal_one]
      exact ⟨le_rfl, le_rfl⟩
    · -- the slope identity is ring arithmetic
      funext i
      fin_cases i
      simp [dotProduct, NonlinDASys.ReducedModel.toNonlinearSys, daeRed, daeSys]
      ring

/-- `x ∈ [3/4, 5/4]`, and `u ∈ [-1/16, 1/16]`. -/
def X₀ : Zonotope D 1 := ⟨1, ![d 1 0], !![d 1 (-2)], zbox 1⟩
def U₀ : Zonotope D 1 := ⟨1, ![d 0 0], !![d 1 (-4)], zbox 1⟩

/-- Eight steps of `1/8`, Taylor order at least `4`, zonotope order `10`. The reduced model is
data the run never reads (`NonlinDASys.reachFloat` is the ordinary run of `model`), so the
computable form is written without it, and `run_eq` is that this is the same run. -/
def run : Option (List (Zonotope D 1)) :=
  model.reachFloat { R0 := X₀, U := U₀, tFinal := 1 }
    { timeStep := d 1 (-3), taylorTerms := 4, zonotopeOrder := 10 }

theorem run_eq : NonlinDASys.reachFloat daeRed model { R0 := X₀, U := U₀, tFinal := 1 }
    { timeStep := d 1 (-3), taylorTerms := 4, zonotopeOrder := 10 } = run := rfl

#eval run.map (·.length)   -- some 8
-- the range of `x` in each window, falling towards the equilibrium `2u = 0`
#eval run.map (·.map fun Z =>
  (toF ((Zonotope.interval Z).inf 0), toF ((Zonotope.interval Z).sup 0)))

/-- The guarantee of the list the run returns (the `#eval` above shows it does): every trajectory
of the algebraic system from `X₀` under `U₀` is, at every time of every window, in the window's
zonotope. -/
theorem run_outer {Rs : List (Zonotope D 1)} (h : run = some Rs) :
    ∃ N : ℕ, (N : ℝ) * toReal (d 1 (-3) : D) = ((1 : ℚ) : ℝ) - ((0 : ℚ) : ℝ) ∧ Rs.length = N ∧
      ∀ {x : ℝ → Vec ℝ 1} {y : ℝ → Vec ℝ 1} {u : ℝ → Vec ℝ 1},
        daeSys.Trajectory (S := fun k => Set (Vec ℝ k)) (Set.Icc 0 (((1 : ℚ) : ℝ) - ((0 : ℚ) : ℝ)))
          X₀.construct U₀.construct x y u →
        ∀ (k : ℕ) (hk : k < Rs.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal (d 1 (-3) : D))
          (((k : ℝ) + 1) * toReal (d 1 (-3) : D)), x t ∈ Rs[k].construct :=
  NonlinDASys.reachFloat_outer daeRed model_encloses (run_eq.trans h)

end CORALean.Examples.NonlinDASysFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
