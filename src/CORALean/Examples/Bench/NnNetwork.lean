import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContSet.HPolytope.Float.Instances
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.Examples.Bench.NnNaive
import CORALean.NN.Instances
import CORALean.NN.Layers.Instances
import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Layers.Operations.Basic
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.NN.Layers.Theorems.LinearEncloses
import CORALean.NN.Layers.Theorems.ReluEncloses
import CORALean.NN.Operations.Enclose
import CORALean.NN.Theorems.EncloseOuter
import CORALean.NN.Theorems.HoldsOfCheck
import CORALean.Specification.Instances

/-!
# `nn-float32`'s network: `y = relu(x + 2^24) - 2^24` on `X = [-7/4, 1/4]`

Over the reals the network is the identity on `X`, so `y ≤ 0` fails on `(0, 1/4]`;
`xStar = 1/4` gives `y = 1/4`. In binary32 every point of `X` is absorbed by
`2^24`, whose neighbours are `2^24 - 1` and `2^24 + 2`: the hidden neuron's bounds
round to `[2^24 - 2, 2^24]`, `y`'s to `[-2, 0]`, and a verifier that trusts them
certifies `y ≤ 0`. The zonotope's center `-3/4` rounds to `2^24 - 1` the same way.

Every weight, bias and bound is data here, exact, and read into whichever scalar
an analysis runs at: `NnNaive`'s binary32, or `network` at `Dyadic 24` and
`Float`, the verified enclosure through `NeuralNetwork.enclose`. `network_encloses`
says what that enclosure is sound for -- the exact map the stored weights denote,
the ReLU exact -- and `network_mem_enclose` is `enclose_outer` read at it.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       27-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench.Nn

open CORALean CORALean.Float ContSet
open scoped Matrix


/-! ## The example, exact -/

/-- `x ↦ x + 2^24`: the one hidden neuron. -/
def layer₁ : Layer ExactDyadic := ⟨#[#[⟨1, 0⟩]], #[⟨1, 24⟩]⟩

/-- `h ↦ h - 2^24`: the output, which undoes the shift exactly over ℝ. -/
def layer₂ : Layer ExactDyadic := ⟨#[#[⟨1, 0⟩]], #[⟨-1, 24⟩]⟩

/-- `X = [-7/4, 1/4]`, center `-3/4` and radius `1`. -/
def boxLo : Array ExactDyadic := #[⟨-7, -2⟩]
def boxHi : Array ExactDyadic := #[⟨1, -2⟩]

/-- The counterexample: `y(1/4) = 1/4 > 0`. -/
def xStar : Array ExactDyadic := #[⟨1, -2⟩]

/-- The property is `y ≤ threshold`. -/
def threshold : ExactDyadic := ExactDyadic.zero

/-- Center and radius of `[lo, hi]`, exact: halving a dyadic is an exponent shift. -/
def centerRadius (lo hi : ExactDyadic) : ExactDyadic × ExactDyadic :=
  let half : ExactDyadic := ⟨1, -1⟩
  ((lo.add hi).mul half, (hi.add lo.neg).mul half)


/-! ## The same network, at a sound scalar -/

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `L`'s weights at `𝕋`, an `m × n` matrix. -/
def Layer.mat (inst : ExactDyadic → 𝕋) (L : Layer ExactDyadic) (m n : ℕ) : Mat 𝕋 m n :=
  fun i j => inst ((L.W.getD i #[]).getD j ExactDyadic.zero)

def Layer.vec (inst : ExactDyadic → 𝕋) (L : Layer ExactDyadic) (m : ℕ) : Vec 𝕋 m :=
  fun i => inst (L.b.getD i ExactDyadic.zero)

/-- `X` as a float zonotope: its center, one generator per coordinate, no error. -/
def inputZonotope (inst : ExactDyadic → 𝕋) : Zonotope (Vec 𝕋 1) :=
  let (c, r) := centerRadius (boxLo.getD 0 ExactDyadic.zero) (boxHi.getD 0 ExactDyadic.zero)
  ⟨1, fun _ => inst c, fun _ _ => inst r, ⟨fun _ => inst ExactDyadic.zero,
    fun _ => inst ExactDyadic.zero⟩⟩

def inputBox (inst : ExactDyadic → 𝕋) : Interval (Vec 𝕋 1) :=
  ⟨fun i => inst (boxLo.getD i ExactDyadic.zero), fun i => inst (boxHi.getD i ExactDyadic.zero)⟩

/-- `y ≤ threshold` as a one-row halfspace, the safe set `Specification.check` tests. -/
def spec (inst : ExactDyadic → 𝕋) : Specification (HPolytope 𝕋 (Vec 𝕋 1)) :=
  .safeSet ⟨1, fun _ _ => inst ExactDyadic.one, fun _ => inst threshold, 0, fun i => i.elim0,
    fun i => i.elim0, fun _ => FloatOps.zero, fun _ => FloatOps.zero, Interval.origin _⟩

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n h : ℕ}

/-- Affine, ReLU, affine, over any set representation the layers accept. -/
def network (W₁ : Mat 𝕋 h n) (b₁ : Vec 𝕋 h) (W₂ : Mat 𝕋 1 h) (b₂ : Vec 𝕋 1) :
    NeuralNetwork S n 1 :=
  .layer (⟨W₁, b₁⟩ : LinearLayer 𝕋 n h)
    (.layer (⟨reluSlope, rfl⟩ : ReluLayer 𝕋 h h) (.layer (⟨W₂, b₂⟩ : LinearLayer 𝕋 h 1) .output))

/-- What `network` encloses: the exact affine maps its stored weights denote,
around the exact ReLU. -/
theorem network_encloses (W₁ : Mat 𝕋 h n) (b₁ : Vec 𝕋 h) (W₂ : Mat 𝕋 1 h) (b₂ : Vec 𝕋 1) :
    (network (S := S) W₁ b₁ W₂ b₂).Encloses fun x =>
      Scalar.toRealMat W₂ *ᵥ (fun i => Real.relu ((Scalar.toRealMat W₁ *ᵥ x
        + Scalar.toRealVec b₁) i)) + Scalar.toRealVec b₂ := by -- --- PROOF ---
  delta network
  exact .layer (Layer.linear_encloses W₁ b₁)
    (.layer (Layer.relu_encloses reluSlope)
      (.layer (Layer.linear_encloses W₂ b₂) (.output fun _ => rfl) fun _ => rfl) fun _ => rfl)
    fun _ => rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- The soundness corollary `nn-float32` reports on: every exact output over the
input set lies in the computed enclosure, whatever the precision. -/
theorem network_mem_enclose (W₁ : Mat 𝕋 h n) (b₁ : Vec 𝕋 h) (W₂ : Mat 𝕋 1 h)
    (b₂ : Vec 𝕋 1) (X : S n) {x : Vec ℝ n} (hx : x ∈ construct X) : -- --- STMT ---
    Scalar.toRealMat W₂ *ᵥ (fun i => Real.relu ((Scalar.toRealMat W₁ *ᵥ x
        + Scalar.toRealVec b₁) i)) + Scalar.toRealVec b₂
      ∈ construct ((network (S := S) W₁ b₁ W₂ b₂).enclose X) :=
  (network_encloses W₁ b₁ W₂ b₂).enclose_outer X x hx

end CORALean.Bench.Nn


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
