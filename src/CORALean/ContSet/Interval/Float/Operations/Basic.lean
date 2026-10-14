module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Interval.Float.Operations.CoshHi
public import CORALean.ContSet.Interval.Float.Operations.Mask
public import CORALean.ContSet.Interval.Float.Operations.Recip
public import CORALean.ContSet.Interval.Float.Operations.Times
public import CORALean.Global.Float.Atanh
public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.FloatOps
public import CORALean.Global.Float.Hyperbolic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Interval.Set.Defs

@[expose] public section

/-!
# `ContSet/Interval/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ======================================  `Interval.abs`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- `max 0 (inf, -sup)` and `max (-inf, sup)`; `neg` and `maximum` are exact, so nothing rounds. -/
protected def Interval.abs (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => maximum zero (maximum (I.inf i) (neg (I.sup i)))
  sup := fun i => maximum (neg (I.inf i)) (I.sup i)

end CORALean.Float


-- ====================================  `Interval.append`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} {n₁ n₂ : ℕ}

/-- Two boxes side by side: the product box, in the coordinates of one vector. Nothing rounds, the
bounds are copied. -/
def Interval.append (I₁ : Interval (Vec 𝕋 n₁)) (I₂ : Interval (Vec 𝕋 n₂)) :
    Interval (Vec 𝕋 (n₁ + n₂)) :=
  ⟨Fin.append I₁.inf I₂.inf, Fin.append I₁.sup I₂.sup⟩

end CORALean.Float


-- =====================================  `Interval.atanh`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Increasing, so `atanhDown` at the lower bound and `atanhUp` at the upper one
(`Global/Float/Atanh`). `p` is `logDown`'s range exponent, `k` the number of bisection steps. -/
def Interval.atanh (p k : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => atanhDown p k (I.inf i)
  sup := fun i => atanhUp p k (I.sup i)

end CORALean.Float


-- ===================================  `Interval.centerLo`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The midpoint with the sum rounded down: at most the real midpoint. -/
def Interval.centerLo (I : Interval (Vec 𝕋 n)) : Vec 𝕋 n :=
  fun i => half (addDown (I.inf i) (I.sup i))

end CORALean.Float


-- ====================================  `Interval.coshLo`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]

/-- The lower bound of `cosh` over `[lb, ub]`, as the real `Interval.coshLo`: `cosh ub` if the range
lies left of `0`, `cosh lb` if right of it, and `1` if it contains `0`. `le` answers only `true`
reliably, which is enough: the third case is a bound at every range. -/
def Interval.coshLo (p : ℕ) (lb ub : 𝕋) : 𝕋 :=
  if le ub zero = true then coshDown p ub else if le zero lb = true then coshDown p lb else one

end CORALean.Float


-- =====================================  `Interval.cosh`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- CORA's `@interval/cosh`, coordinate by coordinate, over `coshLo` and `coshHi`. -/
def Interval.cosh (p : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => Interval.coshLo p (I.inf i) (I.sup i)
  sup := fun i => Interval.coshHi p (I.inf i) (I.sup i)

end CORALean.Float


-- =====================================  `Interval.diag`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- A rearrangement: the diagonal matrix of a vector box has the float `zero` off the diagonal,
so nothing is rounded. -/
def Interval.diag (I : Interval (Vec 𝕋 n)) : Interval (Mat 𝕋 n n) where
  inf := fun i j => if i = j then I.inf i else zero
  sup := fun i j => if i = j then I.sup i else zero

end CORALean.Float


-- ====================================  `Interval.diagVec`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} {n : ℕ}

/-- A rearrangement: the diagonal of a matrix box is read off, so nothing is rounded. -/
def Interval.diagVec (I : Interval (Mat 𝕋 n n)) : Interval (Vec 𝕋 n) where
  inf := fun i => I.inf i i
  sup := fun i => I.sup i i

end CORALean.Float


-- =====================================  `Interval.EBox`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- A box with possibly infinite ends, for the results (`Inf`, `lift_`, `dirac`) a floating-point
scalar cannot store: a bound is a float, or `none` for `-∞` (lower) or `∞` (upper). -/
structure Interval.EBox (𝕋 : Type) (n : ℕ) where
  lo : Fin n → Option 𝕋
  hi : Fin n → Option 𝕋

end CORALean.Float


-- ================================  `Interval.EBox.construct`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The points whose every coordinate lies above each stored lower bound and below each stored upper
bound. -/
def Interval.EBox.construct (B : Interval.EBox 𝕋 n) : Set (Vec ℝ n) :=
  {x | ∀ i, (∀ l, B.lo i = some l → toReal l ≤ x i) ∧ (∀ u, B.hi i = some u → x i ≤ toReal u)}

end CORALean.Float


-- =====================================  `Interval.empty`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The crossed box, lower bound `one` and upper bound `zero` in every coordinate. -/
def Interval.empty (n : ℕ) : Interval (Vec 𝕋 n) where
  inf := fun _ => one
  sup := fun _ => zero

end CORALean.Float


-- =================================  `Interval.enclosePoints`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The coordinatewise minimum and maximum of a family of `k` points. Exact: `minimum` and `maximum`
round nothing. -/
def Interval.enclosePoints {k : ℕ} (p : Fin k → Vec 𝕋 n) : Interval (Vec 𝕋 n) where
  inf := fun i => minimumOver fun l => p l i
  sup := fun i => maximumOver fun l => p l i

end CORALean.Float


-- ======================================  `Interval.exp`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Monotone, so `expDown` at the lower bound and `expUp` at the upper one. `p` is the precision of
the two enclosures (`Global/Float/Exp`). -/
def Interval.exp (p : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => expDown p (I.inf i)
  sup := fun i => expUp p (I.sup i)

end CORALean.Float


-- =====================================  `Interval.halve`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Both bounds halved, which is exact in a binary format (`half` only moves the exponent), so no
outward rounding is needed. -/
def Interval.halve (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => half (I.inf i)
  sup := fun i => half (I.sup i)

end CORALean.Float


-- ======================================  `Interval.Inf`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- CORA's `interval.Inf(n)`: `(-∞, ∞)ⁿ`, no bound stored in any coordinate. -/
def Interval.Inf (n : ℕ) : Interval.EBox 𝕋 n := ⟨fun _ => none, fun _ => none⟩

end CORALean.Float


-- ====================================  `Interval.infimum`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

/-- The stored lower bound. -/
def Interval.infimum {α : Type} (I : Interval α) : α := I.inf

end CORALean.Float


-- =================================  `Interval.intersection`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- Coordinatewise and exactly. Nothing rounds: choosing the larger of two stored
lower bounds, or the smaller of two upper ones, returns one of them. -/
def Interval.intersection (I₁ I₂ : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun j => maximum (I₁.inf j) (I₂.inf j)
  sup := fun j => minimum (I₁.sup j) (I₂.sup j)

end CORALean.Float


-- ======================================  `Interval.le`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The containment test at float, one `FloatOps.le` per bound. `le` is certified in one direction
only, so `true` is a proof and `false` is no refutation. -/
protected def Interval.le (I J : Interval (Vec 𝕋 n)) : Bool :=
  (List.finRange n).all fun j => FloatOps.le (J.inf j) (I.inf j) && FloatOps.le (I.sup j) (J.sup j)

end CORALean.Float


-- ====================================  `Interval.linComb`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       19-August-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The box around both, as over ℝ. Exact: `minimum` and `maximum` pick one of the
two stored floats and invent no digits, so neither bound rounds. -/
def Interval.linComb (I₁ I₂ : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => minimum (I₁.inf i) (I₂.inf i)
  sup := fun i => maximum (I₁.sup i) (I₂.sup i)

end CORALean.Float


-- ==================================  `Interval.matResidual`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}

/-- `Interval.residual` at `Mat 𝕋 m n`: the box an operation owes when it stores a
rounded matrix, entrywise `[lo - stored, hi - stored]`. -/
def Interval.matResidual (lo hi stored : Mat 𝕋 m n) : Interval (Mat 𝕋 m n) :=
  ⟨fun i j => subDown (lo i j) (stored i j), fun i j => subUp (hi i j) (stored i j)⟩

end CORALean.Float


-- ======================================  `Interval.max`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The coordinatewise larger of the bounds. `maximum` is exact, choosing between two floats, so
nothing is rounded. -/
protected def Interval.max (I₁ I₂ : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => maximum (I₁.inf i) (I₂.inf i)
  sup := fun i => maximum (I₁.sup i) (I₂.sup i)

end CORALean.Float


-- ======================================  `Interval.min`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The coordinatewise smaller of the bounds. `minimum` is exact, choosing between two floats, so
nothing is rounded. -/
protected def Interval.min (I₁ I₂ : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => minimum (I₁.inf i) (I₂.inf i)
  sup := fun i => minimum (I₁.sup i) (I₂.sup i)

end CORALean.Float


-- =====================================  `Interval.minus`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Each bound rounds away from the interval: `inf` down, `sup` up. -/
def Interval.minus (I₁ I₂ : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => subDown (I₁.inf i) (I₂.sup i)
  sup := fun i => subUp (I₁.sup i) (I₂.inf i)

end CORALean.Float


-- ====================================  `Interval.mtimes`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}

/-- `minimum`/`maximum` absorb the sign of `M i k` as `min`/`max` do over ℝ, and
each bound rounds away from the interval. -/
def Interval.mtimes (M : Mat 𝕋 m n) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 m) where
  inf := fun i => sumDown fun k => minimum (mulDown (M i k) (I.inf k)) (mulDown (M i k) (I.sup k))
  sup := fun i => sumUp fun k => maximum (mulUp (M i k) (I.inf k)) (mulUp (M i k) (I.sup k))

end CORALean.Float


-- =================================  `Interval.nonemptyHull`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The upper bound raised to the lower one wherever the two cross, and left alone elsewhere: the
smallest change that makes the box nonempty, and none at all to one that already is. What a
layer committing to a point of its error box runs on, when nothing proves the box nonempty. -/
def Interval.nonemptyHull (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  ⟨I.inf, fun i => maximum (I.inf i) (I.sup i)⟩

end CORALean.Float


-- ====================================  `Interval.normMag`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The entrywise larger of `|inf|` and `|sup|`, which `absolute` and `maximum` give exactly. -/
def Interval.normMag (I : Interval (Vec 𝕋 n)) : Vec 𝕋 n :=
  fun i => maximum (absolute (I.inf i)) (absolute (I.sup i))

end CORALean.Float


-- ================================  `Interval.ofCenterRadius`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}

/-- CORA's constructor `intervalMatrix(C, Δ)`: the box `[C - Δ, C + Δ]` as an interval matrix, each
entry's lower bound rounded down and its upper bound up so the stored box contains the exact one. -/
def Interval.ofCenterRadius (c r : Mat 𝕋 m n) : Interval (Mat 𝕋 m n) where
  inf := fun i j => subDown (c i j) (r i j)
  sup := fun i j => addUp (c i j) (r i j)

end CORALean.Float


-- ======================================  `Interval.or`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The coordinatewise hull. `minimum` and `maximum` are exact, choosing between two floats, so
nothing is rounded. -/
def Interval.or (I₁ I₂ : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => minimum (I₁.inf i) (I₂.inf i)
  sup := fun i => maximum (I₁.sup i) (I₂.sup i)

end CORALean.Float


-- ===================================  `Interval.convHull`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- CORA's `convHull_` ends in `I | S`, so it is `or`. -/
def Interval.convHull (I₁ I₂ : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) := I₁.or I₂

end CORALean.Float


-- ====================================  `Interval.origin`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The point interval at the origin of `𝕋ⁿ`, every bound `zero`. -/
def Interval.origin (n : ℕ) : Interval (Vec 𝕋 n) where
  inf := fun _ => zero
  sup := fun _ => zero

end CORALean.Float


-- =====================================  `Interval.plus`  ====================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Each bound rounds away from the interval: `inf` down, `sup` up. -/
def Interval.plus (I₁ I₂ : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => addDown (I₁.inf i) (I₂.inf i)
  sup := fun i => addUp (I₁.sup i) (I₂.sup i)

end CORALean.Float


-- ====================================  `Interval.project`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}

/-- The bounds at the chosen coordinates; nothing is computed, so nothing rounds. -/
def Interval.project (I : Interval (Vec 𝕋 n)) (dims : Fin m → Fin n) : Interval (Vec 𝕋 m) where
  inf := fun k => I.inf (dims k)
  sup := fun k => I.sup (dims k)

end CORALean.Float


-- ====================================  `Interval.radius`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- CORA's `rad`, half the width. `half` is exact, so the one rounding is the difference, and it
rounds up: the stored radius is at least the real one. -/
def Interval.radius (I : Interval (Vec 𝕋 n)) : Vec 𝕋 n := fun i => half (subUp (I.sup i) (I.inf i))

end CORALean.Float


-- ====================================  `Interval.rdivide`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- `y = 1 ./ denominator; res = numerator .* y`: `times` at the outward-rounded reciprocal box. -/
def Interval.rdivide (numerator denominator : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  let y := denominator.recip
  numerator.times y

end CORALean.Float


-- =============================  `Interval.representsa_emptySet`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The emptiness test at float: some coordinate with `sup` strictly below `inf`, by `ltStrict`. It
certifies emptiness only; a box whose crossing is under the margin is not reported. -/
def Interval.representsa_emptySet (I : Interval (Vec 𝕋 n)) : Bool :=
  (List.finRange n).any fun j => ltStrict (I.sup j) (I.inf j)

end CORALean.Float


-- ==============================  `Interval.representsa_origin`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The origin test at float: each bound is `≤ 0` and `≥ 0`. One direction only, as `le`. -/
def Interval.representsa_origin (I : Interval (Vec 𝕋 n)) : Bool :=
  (List.finRange n).all fun j =>
    FloatOps.le (I.inf j) zero && FloatOps.le zero (I.inf j) &&
    FloatOps.le (I.sup j) zero && FloatOps.le zero (I.sup j)

end CORALean.Float


-- ===============================  `Interval.representsa_point`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The point test at float: both bounds compare `≤` each other in every coordinate. One direction
only, as `le`. -/
def Interval.representsa_point (I : Interval (Vec 𝕋 n)) : Bool :=
  (List.finRange n).all fun j => FloatOps.le (I.sup j) (I.inf j) && FloatOps.le (I.inf j) (I.sup j)

end CORALean.Float


-- ===================================  `Interval.residual`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The box an operation owes when it stores a rounded vector: the intended value
lies in `[lo, hi]` but `stored` was written down, so `[lo - stored, hi - stored]`
covers the difference. -/
def Interval.residual (lo hi stored : Vec 𝕋 n) : Interval (Vec 𝕋 n) :=
  ⟨fun i => subDown (lo i) (stored i), fun i => subUp (hi i) (stored i)⟩

end CORALean.Float


-- =====================================  `Interval.sinh`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Increasing, so `sinhDown` at the lower bound and `sinhUp` at the upper one
(`Global/Float/Hyperbolic`). `p` is the precision of the exponentials. -/
def Interval.sinh (p : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => sinhDown p (I.inf i)
  sup := fun i => sinhUp p (I.sup i)

end CORALean.Float


-- ==================================  `Interval.stlInterval`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- CORA's `@interval/stlInterval`: the one-dimensional box as an STL time interval `[inf, sup]`,
closed at both ends, as the set of times the stored floats denote (no `stlInterval` class is in
the tree). -/
def Interval.stlInterval (I : Interval (Vec 𝕋 1)) : Set ℝ :=
  Set.Icc (toReal (I.inf 0)) (toReal (I.sup 0))

end CORALean.Float


-- =====================================  `Interval.sum₂`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}

/-- CORA's `sum` of an interval matrix along each row: the lower bounds are summed rounding down and
the upper bounds rounding up, so the stored box holds every column sum the exact one does. -/
def Interval.sum₂ (I : Interval (Mat 𝕋 m n)) : Interval (Vec 𝕋 m) where
  inf := fun i => sumDown fun j => I.inf i j
  sup := fun i => sumUp fun j => I.sup i j

end CORALean.Float


-- ===================================  `Interval.supremum`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

/-- The stored upper bound. -/
def Interval.supremum {α : Type} (I : Interval α) : α := I.sup

end CORALean.Float


-- ===================================  `Interval.symmetric`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The box `[-r, r]`, which is what a bound known only in magnitude gives. -/
def Interval.symmetric (r : Vec 𝕋 n) : Interval (Vec 𝕋 n) := ⟨fun i => neg (r i), r⟩

end CORALean.Float


-- =====================================  `Interval.tanh`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Increasing, so `tanhDown` at the lower bound and `tanhUp` at the upper one
(`Global/Float/Hyperbolic`). `p` is the precision of the exponential. -/
def Interval.tanh (p : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => tanhDown p (I.inf i)
  sup := fun i => tanhUp p (I.sup i)

end CORALean.Float


-- =====================================  `Interval.tril`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}

/-- `Interval.mask` at the entries on or below the `K`-th superdiagonal. -/
def Interval.tril (K : ℕ) (I : Interval (Mat 𝕋 m n)) : Interval (Mat 𝕋 m n) :=
  I.mask (fun i j => (j : ℕ) ≤ (i : ℕ) + K)

end CORALean.Float


-- =====================================  `Interval.triu`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}

/-- `Interval.mask` at the entries on or above the `K`-th superdiagonal. -/
def Interval.triu (K : ℕ) (I : Interval (Mat 𝕋 m n)) : Interval (Mat 𝕋 m n) :=
  I.mask (fun i j => (i : ℕ) + K ≤ (j : ℕ))

end CORALean.Float


-- ====================================  `Interval.uminus`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Negation is exact, `neg` flipping a sign bit, so the bounds swap and negate with no rounding. -/
def Interval.uminus (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => neg (I.sup i)
  sup := fun i => neg (I.inf i)

end CORALean.Float


-- =====================================  `Interval.uplus`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

/-- Unary plus, the identity, over any stored ambient type. -/
def Interval.uplus {α : Type} (I : Interval α) : Interval α := I

end CORALean.Float


-- ====================================  `Interval.vertcat`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} {m₁ m₂ n : ℕ}

/-- Stacking the bound matrices moves floats without computing on them, so nothing is rounded. -/
def Interval.vertcat (I : Interval (Mat 𝕋 m₁ n)) (J : Interval (Mat 𝕋 m₂ n)) :
    Interval (Mat 𝕋 (m₁ + m₂) n) where
  inf := Fin.append I.inf J.inf
  sup := Fin.append I.sup J.sup

end CORALean.Float


-- =========================================  `prodUp`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- A right-nested fold of `mulUp`, which is not associative, so it names its bracketing as `sumUp`
does. -/
def prodUp {k : ℕ} (f : Fin k → 𝕋) : 𝕋 := Fin.foldr k (fun i acc => mulUp (f i) acc) one

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
