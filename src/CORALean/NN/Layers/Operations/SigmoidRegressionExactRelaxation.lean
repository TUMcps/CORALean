module

public import CORALean.NN.Layers.Operations.Basic
public import CORALean.NN.Layers.Operations.RegressionSlope
public import CORALean.NN.Layers.Operations.SigmoidEnclosure
public import CORALean.Global.Float.Atanh
public import CORALean.Global.Float.Sqrt
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The sigmoid relaxation at the regression line, with the exact error

CORA's `nnSigmoidLayer.computeApproxError` at order 1: the line is the regression line of
`regressionSlope`, and its error comes from the extremum of `σ t - m t` over the box, which sits at
an end or at `±2 artanh √(1 - 4 m)` [1, Prop. 10]. Here the slope is whatever the floats gave and
the stationary points are enclosed, not computed: `±t₀` lies in a float interval that `atanhUp`,
`atanhDown`, `sqrtUp` and `sqrtDown` bound, `σ t - m t` is bounded on it by monotonicity, and the
candidates join the ends. Outside `(0, 1/4]` there is no stationary point, and none is looked for.

## Inputs
* `k` – reduction depth of the exponential, also the steps of the root and the logarithm

## Output
* relaxation of the sigmoid with the regression slope and the error of its extremum

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../../references/2025/koller-tmlr-set-based-training.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- An upper bound of `σ t - m t` for `t ∈ [a, b]`: `σ` at `b`, `m t` at its smaller end. -/
@[step_of sigmoidRegressionExactRelaxation]
def step_extremumUp (E : Enclosure 𝕋) (m a b : 𝕋) : 𝕋 :=
  subUp (E.enclose b).sup (minimum (mulDown m a) (mulDown m b))

/-- A lower bound of `σ t - m t` for `t ∈ [a, b]`: `σ` at `a`, `m t` at its larger end. -/
@[step_of sigmoidRegressionExactRelaxation]
def step_extremumLo (E : Enclosure 𝕋) (m a b : 𝕋) : 𝕋 :=
  subDown (E.enclose a).inf (maximum (mulUp m a) (mulUp m b))

/-- A lower bound of `t₀ = 2 artanh √(1 - 4 m)`: `artanh` of the root from below, capped at
`1 - 2⁻⁵²` as the logarithm's range `2⁶⁴` requires, and zero where `1 + x` is not certified
positive. -/
@[step_of sigmoidRegressionExactRelaxation]
def step_stationaryLo (k : ℕ) (m : 𝕋) : 𝕋 :=
  let cap := subDown one (Nat.iterate half 52 one)                             -- 1 - 2⁻⁵²
  let s := minimum cap (maximum zero (sqrtDown k (subDown one (nsmulUp 4 m))))  -- √(1-4m) below
  if ltStrict zero (subDown one (neg s)) = true
  then addDown (atanhDown 64 k s) (atanhDown 64 k s) else zero                 -- 2 artanh s

/-- An upper bound of `t₀`: `artanh` of the root from above, or none where the root is not
certified below one. -/
@[step_of sigmoidRegressionExactRelaxation]
def step_stationaryHi (k : ℕ) (m : 𝕋) : Option 𝕋 :=
  let s := sqrtUp k (subUp one (nsmulDown 4 m))                                -- √(1-4m) above
  if ltStrict zero (subDown one s) = true
  then some (addUp (atanhUp 64 k s) (atanhUp 64 k s)) else none                -- 2 artanh s

/-- The part of `[l, u]` that holds `t₀`, or none where it holds none. The two computed ends are
taken in either order, since at `nearest` the lower may exceed the upper by an ulp. -/
@[step_of sigmoidRegressionExactRelaxation]
def step_stationaryBox (k : ℕ) (m l u : 𝕋) : Option (𝕋 × 𝕋) :=
  let t := step_stationaryLo k m
  let a := match step_stationaryHi k m with
    | some h => maximum l (minimum t h)
    | none => maximum l t
  let b := match step_stationaryHi k m with
    | some h => minimum u (maximum t h)
    | none => u
  if ltStrict b a = true then none else some (a, b)

/-- The boxes that hold the stationary points `±t₀` inside `[l, u]`; none where `m ≤ 0` or `m > 1/4`
is certified, since `σ'` takes no such value there. -/
@[step_of sigmoidRegressionExactRelaxation]
def step_candidates (k : ℕ) (m l u : 𝕋) : List (𝕋 × 𝕋) :=
  if le m zero = true || ltStrict one (nsmulDown 4 m) = true then [] else
  let pos := step_stationaryBox k m l u                                        -- t₀
  let ngt := (step_stationaryBox k m (neg u) (neg l)).map fun (a, b) => (neg b, neg a)  -- -t₀
  pos.toList ++ ngt.toList

/-- The largest upper bound of `σ t - m t` over the ends and the candidate boxes. -/
@[step_of sigmoidRegressionExactRelaxation]
def step_extremumHi (E : Enclosure 𝕋) (k : ℕ) (l u : 𝕋) : 𝕋 :=
  let m := regressionSlope E l u
  (step_candidates k m l u).foldl (fun g c => maximum g (step_extremumUp E m c.1 c.2))
    (maximum (step_extremumUp E m l l) (step_extremumUp E m u u))

/-- The smallest lower bound of `σ t - m t` over the ends and the candidate boxes. -/
@[step_of sigmoidRegressionExactRelaxation]
def step_extremumMin (E : Enclosure 𝕋) (k : ℕ) (l u : 𝕋) : 𝕋 :=
  let m := regressionSlope E l u
  (step_candidates k m l u).foldl (fun g c => minimum g (step_extremumLo E m c.1 c.2))
    (minimum (step_extremumLo E m l l) (step_extremumLo E m u u))

/-- The offset: the middle of the two bounds, the way `Relaxation.ofDeriv` takes it. -/
@[step_of sigmoidRegressionExactRelaxation]
def step_extremumMid (E : Enclosure 𝕋) (k : ℕ) (l u : 𝕋) : 𝕋 :=
  half (addUp (step_extremumMin E k l u) (step_extremumHi E k l u))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The regression slope, the middle of the extremum's range as offset, the distance to the further
bound as error. -/
def sigmoidRegressionExactRelaxation (k : ℕ) : Relaxation 𝕋 :=
  let E := sigmoidEnclosure (𝕋 := 𝕋) k
  { slope := regressionSlope E
    offset := step_extremumMid E k
    error := fun l u =>
      let c := step_extremumMid E k l u
      maximum (subUp (step_extremumHi E k l u) c) (subUp c (step_extremumMin E k l u)) }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
