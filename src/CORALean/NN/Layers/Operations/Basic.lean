module

public import CORALean.Global.Float.FloatOps
public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.NN.Layers.Definitions.ScaleRounding
public import CORALean.NN.Layers.Layer
public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.ConjOffsetLow
public import CORALean.NN.Layers.Operations.ExpRelaxation
public import CORALean.NN.Layers.Operations.InvSqrtRootEnclosure
public import CORALean.NN.Layers.Operations.LayerRelaxationCoeffVec
public import CORALean.NN.Layers.Operations.PolyRelaxationFamilyDegOf
public import CORALean.NN.Layers.Operations.PolyRelaxationPadTo
public import CORALean.NN.Layers.Operations.RelaxationOfAntitone
public import CORALean.NN.Layers.Operations.RelaxationOfDeriv
public import CORALean.NN.Layers.Operations.RelaxationOfMonotone
public import CORALean.NN.Layers.Operations.ReluRelaxation
public import CORALean.NN.Layers.Operations.ReluSlope
public import CORALean.NN.Layers.Operations.RootEnclosure
public import CORALean.NN.Layers.Operations.SigmoidSlope
public import CORALean.NN.Layers.Operations.SoftplusEnclosure

@[expose] public section

/-!
# `NN/Layers/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

section

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {N n : ℕ}


-- ======================================  `bracketShift`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)

/-- The midpoint of a bracket.

The bracket's two ends averaged, `half` being exact and the rounding all in the `addUp`. -/
def bracketShift (lo hi : 𝕋) : 𝕋 := half (addUp lo hi)


-- =====================================  `leakyReluEndUp`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      20-October-2026 (Tobias Ladner)

/-- `max (α a) a - m a`, rounded up.

`max (α a) a - m a`, how far leaky ReLU rises above the line of slope `m` at `a`, rounded up. -/
def leakyReluEndUp (α m a : 𝕋) : 𝕋 := subUp (maximum (mulUp α a) a) (mulDown m a)


-- =====================================  `leakyReluGapUp`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The larger of the two ends: the gap over `[l, u]`, by convexity.

Leaky ReLU is convex, so its gap above a line is the larger of its two end values. -/
def leakyReluGapUp (α m l u : 𝕋) : 𝕋 := maximum (leakyReluEndUp α m l) (leakyReluEndUp α m u)


-- =======================================  `mulRangeUp`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- And from above, the same two products the other way.

The mirror of `mulRangeDown`: both products rounded up and the larger. -/
def mulRangeUp (a lo hi : 𝕋) : 𝕋 := maximum (mulUp a lo) (mulUp a hi)


-- ========================================  `sampleHi`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- The greatest sampled value, raised by the slack rounded up.

The greatest sampled value, raised by that same slack. -/
def sampleHi (gUp : Fin (N + 1) → 𝕋) (M dx : 𝕋) : 𝕋 := addUp (maximumOver gUp) (mulUp M dx)


-- =====================================  `squareDerivHi`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `2 u` from above, the derivative's greatest value on the box.

`σ' x = 2x` over `[l, u]` is at most `2 u`, rounded up. -/
def squareDerivHi (_l u : 𝕋) : 𝕋 := addUp u u


-- =====================================  `squareDerivLo`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `2 l` from below, the derivative's least value on the box.

`σ' x = 2x` over `[l, u]` is at least `2 l`, rounded down. -/
def squareDerivLo (l _u : 𝕋) : 𝕋 := addDown l l


-- =======================================  `sumOffDown`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- `∑_{j ≠ i} v j`, the `i`-th term zeroed, rounded down.

The mirror of `sumOffUp`. -/
def sumOffDown (i : Fin n) (v : Fin n → 𝕋) : 𝕋 :=
  sumDown fun j => if j = i then zero else v j

end


section

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  `conjCoeffsDown`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   12-October-2026
-- Reviewed:      ---

/-- The conjugated coefficients `a · bⁱ · p i` (constant shifted by `c`), rounded down.

The mirror of `aux_conjCoeffsUp`, every step rounded down. -/
def conjCoeffsDown (A B : ScaleRounding 𝕋) (c : 𝕋) (p : Fin (m + 1) → 𝕋) : Fin (m + 1) → 𝕋 :=
  fun i =>
    if i = 0 then addDown (A.down (B.down^[(i : ℕ)] (p i))) c else A.down (B.down^[(i : ℕ)] (p i))


-- ====================================  `Enclosure.exact`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- `σ` itself at both ends, which only ℝ stores. -/
def Enclosure.exact (σ : ℝ → ℝ) : Enclosure ℝ := ⟨fun a => ⟨σ a, σ a⟩⟩


-- =================================  `invSqrtRootRelaxation`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The slope-zero relaxation of an antitone function at that enclosure.

The slope-zero relaxation of the antitone `invSqrt` at `invSqrtRootEnclosure`. -/
def invSqrtRootRelaxation (p : ℕ) : Relaxation 𝕋 := Relaxation.ofAntitone (invSqrtRootEnclosure p)


-- ===============================  `LayerRelaxation.coeffList`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- The coefficient vectors, lowest degree first.

The coefficient vectors as `PolyZonotope.evalPoly` takes them, lowest degree first. -/
def LayerRelaxation.coeffList (P : LayerRelaxation 𝕋 n m) (I : Interval (Vec 𝕋 n)) :
    List (Vec 𝕋 n) := List.ofFn (P.coeffVec I)


-- =============================  `PolyRelaxationFamily.atPattern`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- Each neuron's own fit at its own level, padded to the common degree.

Each neuron's own fit at its own level, padded to the common degree, which is exact. -/
def PolyRelaxationFamily.atPattern (F : PolyRelaxationFamily 𝕋) (t : OrderPattern n) :
    LayerRelaxation 𝕋 n (F.degOf t) :=
  fun i => (F.rel (t i)).padTo (F.degOf t)


-- ===============================  `Relaxation.conjOffsetHigh`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- The upper rounding of `ra * R.offset + c`.

`ra · offset + c`, rounded up, the mirror of `conjOffsetLow`. -/
def Relaxation.conjOffsetHigh (R : Relaxation 𝕋) (A B : ScaleRounding 𝕋) (c l u : 𝕋) : 𝕋 :=
  addUp (A.up (R.offset (B.down l) (B.up u))) c


-- =================================  `Relaxation.conjOffset`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- The offset chosen: the midpoint of its two roundings.

The midpoint of the two roundings of `ra · offset + c`, as for the slope. -/
def Relaxation.conjOffset (R : Relaxation 𝕋) (A B : ScaleRounding 𝕋) (c l u : 𝕋) : 𝕋 :=
  half (addUp (Relaxation.conjOffsetLow R A B c l u) (Relaxation.conjOffsetHigh R A B c l u))


-- ================================  `Relaxation.conjOffsetGap`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- The distance from the stored offset to the further rounding, rounded up.

The offset's counterpart of `conjSlopeGap`. -/
def Relaxation.conjOffsetGap (R : Relaxation 𝕋) (A B : ScaleRounding 𝕋) (c l u : 𝕋) : 𝕋 :=
  maximum (subUp (Relaxation.conjOffsetHigh R A B c l u) (Relaxation.conjOffset R A B c l u))
    (subUp (Relaxation.conjOffset R A B c l u) (Relaxation.conjOffsetLow R A B c l u))


-- ================================  `Relaxation.conjSlopeHigh`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- The upper rounding of `ra * rb * R.slope`, `rb`'s box map folded in first.

The upper rounding of `ra · rb · λ`, the mirror of `conjSlopeLow`. -/
def Relaxation.conjSlopeHigh (R : Relaxation 𝕋) (A B : ScaleRounding 𝕋) (l u : 𝕋) : 𝕋 :=
  A.up (B.up (R.slope (B.down l) (B.up u)))


-- =====================================  `rootRelaxation`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The slope-zero relaxation of a monotone function at that enclosure.

The slope-zero relaxation of the monotone square root at `rootEnclosure`. -/
def rootRelaxation (p : ℕ) : Relaxation 𝕋 := Relaxation.ofMonotone (rootEnclosure p)


-- ==================================  `ScaleRounding.exact`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- Multiplication by `r` itself, both ways, which only ℝ stores. -/
def ScaleRounding.exact (r : ℝ) : ScaleRounding ℝ := ⟨(r * ·), (r * ·)⟩


-- ===============================  `sigmoidCurvatureRelaxation`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- `Relaxation.ofDeriv` at the sigmoid's derivative bracket and its clamped secant, `σ` at the
box's left end supplied by the same enclosure. -/
def sigmoidCurvatureRelaxation (E : Enclosure 𝕋) : Relaxation 𝕋 :=
  Relaxation.ofDeriv E (sigmoidDerivLo E) (sigmoidDerivHi E) (sigmoidSlope E)


-- ===================================  `softplusRelaxation`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The slope-zero relaxation at that enclosure.

`Relaxation.ofMonotone` at `softplusEnclosure`: softplus is monotone for a positive sharpness. -/
def softplusRelaxation (β : 𝕋) (k nl kl : ℕ) : Relaxation 𝕋 :=
  Relaxation.ofMonotone (softplusEnclosure β k nl kl)


-- ====================================  `squareEnclosure`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `a·a` rounded each way.

`a·a` rounded each way: `x²` at a stored value. -/
def squareEnclosure : Enclosure 𝕋 where
  enclose a := ⟨mulDown a a, mulUp a a⟩

end


section

universe u

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}
  {f : Vec ℝ n → Vec ℝ m} {g : Vec ℝ m → Vec ℝ k}


-- ====================================  `Enclose.toLayer`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---

/-- One layer of a kind, the kind forgotten, which is how a network holds it. -/
def Enclose.toLayer {L : ℕ → ℕ → Type u} [Enclose L S] (l : L n m) : Layer S n m where
  enclose := Enclose.enclose l


-- =======================================  `Layer.comp`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---

/-- Applied right to left, as composition is written. -/
def Layer.comp (L₂ : Layer S m k) (L₁ : Layer S n m) : Layer S n k where
  enclose s := L₂.enclose (L₁.enclose s)


-- =====================================  `Layer.identity`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---

/-- Carries a coordinate past a block untouched, which is how a skip connection
is written: the skipped coordinates travel in the same set as the rest, so the
dependency between them survives. -/
def Layer.identity (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) : Layer S n n where
  enclose s := s

end


section

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =======================================  `Layer.exp`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `nnExpLayer`: `Layer.activation` at `expRelaxation k`. Sound on the sets whose box stays
under `2ᵏ/2`, which is `Float.expUp`'s own range. -/
def Layer.exp (k : ℕ) : Layer S n n := Layer.activation (expRelaxation k)


-- ===================================  `Layer.invSqrtRoot`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `nnInvSqrtRootLayer`: `Layer.activation` at `invSqrtRootRelaxation p`. -/
def Layer.invSqrtRoot (p : ℕ) : Layer S n n := Layer.activation (invSqrtRootRelaxation p)


-- =======================================  `Layer.root`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `nnRootLayer`: `Layer.activation` at `rootRelaxation p`. Sound on every set,
`Real.sqrt` being `0` below `0` and `sqrtUp`/`sqrtDown` total. -/
def Layer.root (p : ℕ) : Layer S n n := Layer.activation (rootRelaxation p)

end

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
