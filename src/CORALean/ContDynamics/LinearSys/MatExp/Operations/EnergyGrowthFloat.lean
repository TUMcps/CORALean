module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.QuadBoundUp
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.EnergyWeightFloat
public import CORALean.ContSet.Ellipsoid.Float.Operations.CholFactor
public import CORALean.ContSet.Ellipsoid.Float.Operations.PsdCheck
public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.MaterialiseMat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `MatExp.energyGrowthFloat`, a checked growth bound `c e^{rt}` of `e^{tA}` from an energy weight

The weight `P` of `MatExp.energyWeightFloat` is checked in the powers of two `σ ≈ 1/√P_ii`, where it
is well conditioned: `P̃ = ΣPΣ` must be symmetric, and with `Ã = Σ⁻¹AΣ` between two roundings
`P̃ - aI` (`a = 2⁻ᵏ`, the first `k ≤ 40` that passes) and `2rP̃ - P̃Ã - (P̃Ã)ᵀ` certified positive
semi-definite (`Ellipsoid.psdCheck` with `Ellipsoid.cholFactor`). Then `‖e^{tÃ}‖₂ ≤ √(b/a) e^{rt}`,
`b` Gershgorin's bound of `P̃`, and in the scales `s`, `‖S⁻¹e^{tA}S‖ ≤ c e^{rt}` with
`c = √(b/a) maxᵢ σᵢ/sᵢ √(Σⱼ (sⱼ/σⱼ)²)`. Cost: the factors and `P̃Ã`, once per run. Scales `σ`
for the whole run would give a smaller `c` (`√n √(b/a)`); `s` stays the balanced one.

## Inputs
* `A` – float system matrix
* `s` – positive float scales
* `r` – positive float rate

## Output
* `c`, if the weight is accepted
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The power of two `σ` with `σ² p` in `[1/2, 2)`, `fuel` doublings or halvings at most. -/
@[step_of MatExp.energyGrowthFloat]
def MatExp.step_energyScaleFloat : ℕ → 𝕋 → 𝕋 → 𝕋
  | 0, _, σ => σ
  | fuel + 1, p, σ =>
    let two : 𝕋 := addUp one one
    let w := mulUp (mulUp σ σ) p
    if le two w then MatExp.step_energyScaleFloat fuel p (half σ)
    else if ltStrict (mulUp two w) one then MatExp.step_energyScaleFloat fuel p (addUp σ σ)
    else σ

/-- `X` is certified positive semi-definite by the factor of its lower bounds without the coupling
of the first `h` indices to the others: no fill, and the coupling (rounding only) is the check's. -/
@[step_of MatExp.energyGrowthFloat]
def MatExp.step_energyPsdFloat (h : ℕ) (X : Interval (Mat 𝕋 n n)) : Bool :=
  Ellipsoid.psdCheck X
    (Ellipsoid.cholFactor 64 fun i j => if decide (i.val < h) = decide (j.val < h) then X.inf i j
      else zero)


/-- The first shift `a = 2⁻ᵏ`, `1 ≤ k < 41`, with `P̃ - aI` certified positive semi-definite. -/
@[step_of MatExp.energyGrowthFloat]
def MatExp.step_energyShiftFloat (h : ℕ) (Pt : Mat 𝕋 n n) : Option 𝕋 :=
  (List.range' 1 40).findSome? fun k =>
    let a : 𝕋 := half^[k] one
    let X : Interval (Mat 𝕋 n n) := ⟨fun i j => if i = j then subDown (Pt i j) a else Pt i j,
      fun i j => if i = j then subUp (Pt i j) a else Pt i j⟩
    if MatExp.step_energyPsdFloat h X then some a else none

/-- `2rP̃ - P̃Ã - (P̃Ã)ᵀ` is certified positive semi-definite, `Ã` within `At`. -/
@[step_of MatExp.energyGrowthFloat]
def MatExp.step_energyRateFloat (h : ℕ) (Pt : Mat 𝕋 n n) (At : Interval (Mat 𝕋 n n)) (r : 𝕋) :
    Bool :=
  let M := (Interval.matMul (Interval.point Pt) At).materialiseMat
  MatExp.step_energyPsdFloat h (⟨fun i j =>
      subDown (subDown (addDown (mulDown r (Pt i j)) (mulDown r (Pt i j))) (M.sup i j)) (M.sup j i),
    fun i j => subUp (subUp (addUp (mulUp r (Pt i j)) (mulUp r (Pt i j))) (M.inf i j))
      (M.inf j i)⟩ : Interval (Mat 𝕋 n n)).materialiseMat

/-- `c = √(b/a) maxᵢ σᵢ/sᵢ √(Σⱼ (sⱼ/σⱼ)²)`, `b` Gershgorin's bound of `P̃`. -/
@[step_of MatExp.energyGrowthFloat]
def MatExp.step_energyFactorFloat (s σ : Vec 𝕋 n) (Pt : Mat 𝕋 n n) (a : 𝕋) : 𝕋 :=
  let w := sqrtUp 64 (sumUp fun j => let x := divUp (s j) (σ j); mulUp x x)
  mulUp (mulUp (sqrtUp 64 (divUp (Krylov.quadBoundUp Pt) a))
    (maximumOver fun i => divUp (σ i) (s i))) w


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The weight in the scales `σ`, its two checks, and the factor `c`. -/
def MatExp.energyGrowthFloat (A : Mat 𝕋 n n) (s : Vec 𝕋 n) (r : 𝕋) : Option 𝕋 := do
  let (h, P) ← MatExp.energyWeightFloat A r
  let σ : Vec 𝕋 n :=                                                     -- `σᵢ ≈ 1/√P_ii`
    (Interval.point fun i => MatExp.step_energyScaleFloat 64 (P i i) one).materialise.sup
  -- `Ã = Σ⁻¹AΣ` between two roundings, `P̃ = ΣPΣ` as rounded
  let At : Interval (Mat 𝕋 n n) := (⟨fun i j => divDown (mulDown (A i j) (σ j)) (σ i),
    fun i j => divUp (mulUp (A i j) (σ j)) (σ i)⟩ : Interval (Mat 𝕋 n n)).materialiseMat
  let Pt : Mat 𝕋 n n :=
    (Interval.point fun i j => mulUp (mulUp (σ i) (P i j)) (σ j)).materialiseMat.sup
  if !(decide (0 < n) && (List.finRange n).all fun i => ltStrict zero (σ i) &&
      (List.finRange n).all fun j => le (Pt i j) (Pt j i)) then none else
  let a ← MatExp.step_energyShiftFloat h Pt
  if MatExp.step_energyRateFloat h Pt At r then some (MatExp.step_energyFactorFloat s σ Pt a)
  else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
