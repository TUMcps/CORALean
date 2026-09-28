import CORALean.ContSet.Interval.Float.Instances
import CORALean.Examples.Bench.MnistParse
import CORALean.NN.Instances
import CORALean.NN.Layers.Instances
import CORALean.NN.Layers.Operations.Relu
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.NN.Operations.Enclose
import CORALean.NN.Theorems.EncloseOuterEval

/-!
# `mnistfc`'s graph, at a sound scalar, with weights that may not fit it

`SOURCES.md` gives the graph: `Flatten -> (Gemm -> Relu)* -> Gemm`, no input
normalisation; `MnistParse.lean` decodes every `float32` bit pattern exactly,
and this file reads that value into `𝕋` and propagates it.

At `p ≥ 24` bits every weight/bias already sits on `𝕋`'s grid; narrower it
does not, and `NN/Layers/` has no interval-weight linear layer (checked:
`Linear`/`LinearWithError` both take a plain `Mat 𝕋 m n`) -- but
`.../Interval/Float` already instantiates `Mtimes` at an *interval* matrix
family (`mtimesIntervalMat`, built for `LinParamSys`'s uncertain system
matrix). `affineLayer` reuses that: `W`/`b` rounded outward with
`mulDown`/`mulUp` against `one`, a no-op on the grid, sound at every
precision, `fitsPrecision` checked nowhere here. `buildChain` folds the
layers into a `NeuralNetwork`, sound via the library's own
`NeuralNetwork.enclose_outer`; `runLayers` (a box, not a zonotope -- see its
own docstring for why) is the same fold as a loop. `k / 255` is not dyadic,
so `inputBox` encloses it, both bounds rounded outward.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   28-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench.Mnist

open CORALean CORALean.Float ContSet Plus Mtimes Float.OfInterval Float.SoundFloatArithmetic
  Float.FloatOps
open scoped Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


/-! ## Rounding a weight (or a pixel ratio) outward to `𝕋`'s grid -/

theorem mulDown_one_le (x : 𝕋) : toReal (mulDown x one) ≤ toReal x := by
  have h := mulDown_le_mul x one
  rwa [toReal_one, mul_one] at h

theorem le_mulUp_one (x : 𝕋) : toReal x ≤ toReal (mulUp x one) := by
  have h := mul_le_mulUp x one
  rwa [toReal_one, mul_one] at h

/-- `W`, read outward: exact at any precision that already holds it (every
`binary32`-or-wider run here), an interval of one ULP otherwise. -/
def outMat {m n : ℕ} (W : Mat 𝕋 m n) : Interval (Mat 𝕋 m n) :=
  ⟨fun i j => mulDown (W i j) one, fun i j => mulUp (W i j) one⟩

def outVec {m : ℕ} (b : Vec 𝕋 m) : Interval (Vec 𝕋 m) :=
  ⟨fun i => mulDown (b i) one, fun i => mulUp (b i) one⟩

theorem mem_outMat {m n : ℕ} (W : Mat 𝕋 m n) : toRealMat W ∈ (outMat W).construct :=
  fun p => ⟨mulDown_one_le (W p.1 p.2), le_mulUp_one (W p.1 p.2)⟩

theorem mem_outVec {m : ℕ} (b : Vec 𝕋 m) : toRealVec b ∈ (outVec b).construct :=
  fun i => ⟨mulDown_one_le (b i), le_mulUp_one (b i)⟩


/-! ## The affine layer, weights rounded outward -/

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Mtimes (fun m n => Interval (Mat 𝕋 m n)) S] [Float.IntervalOuter S 𝕋]
  [Float.OfInterval S 𝕋] {n m : ℕ}

/-- CORA's affine layer, `x ↦ W x + b`, at `outMat W`/`outVec b` rather than
the plain `Mtimes` instance -- sound at every precision, exact where `W`/`b`
already sit on `𝕋`'s grid. -/
def affineLayer (W : Mat 𝕋 m n) (b : Vec 𝕋 m) : Layer S n m where
  enclose s := plus (mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (outMat W) s)
    (ofInterval (outVec b))

set_option linter.unusedSectionVars false in
theorem affineLayer_sound (W : Mat 𝕋 m n) (b : Vec 𝕋 m) :
    (affineLayer (S := S) W b).Sound fun x => toRealMat W *ᵥ x + toRealVec b :=
  ⟨fun s _x hx => plus_outer _ _ (Set.add_mem_add
    (Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (outMat W) s
      (Set.mem_biUnion (mem_outMat W) (Set.mem_image_of_mem _ hx)))
    (ofInterval_outer _ (mem_outVec b)))⟩

/-- The packed form `NeuralNetwork.layer` takes: `affineLayer`'s propagation, at
the exact affine map its rounded-outward weights still enclose. -/
def affineSoundLayer (W : Mat 𝕋 m n) (b : Vec 𝕋 m) : SoundLayer S n m where
  eval := Erased.mk fun x => toRealMat W *ᵥ x + toRealVec b
  enclose := (affineLayer (S := S) W b).enclose
  enclose_outer s := by
    rw [Erased.out_mk]
    exact (affineLayer_sound W b).image_subset s


/-! ## Reading a decoded layer's weights into `𝕋`

`Vec`/`Mat` are function types (`Fin n → 𝕋`, `Fin m → Fin n → 𝕋`); a *named
declaration* whose result is a function type is compiled eta-expanded to
that further arity (`Global/Tensor.lean`'s own docstring), so a `def`
building an array and returning a bare `Mat`/`Vec` over it does not cache
that array across reads -- every `(i, j)` read recomputes the whole thing,
turning an `O(rows * cols)` materialisation into `O((rows * cols)²)`. Wrapping
the result in a one-field structure (`MatBox`/`VecBox`) avoids it: the
`def` then ends in a structure type, is not eta-expanded, and `.get`
projects the array-backed closure back out as an ordinary value.

`Array.getD`'s default is a plain argument, and Lean evaluates arguments
strictly -- a default of `v i`/`M i j` would still force the original,
unmaterialised closure on *every* read, buying nothing. `zero` costs
nothing to force instead, and is never actually returned: `arr` always has
exactly `n` (or `m`) entries, so a caller's own `Fin`-bounded index never
falls outside it. -/

structure VecBox (𝕋 : Type) (n : ℕ) where get : Vec 𝕋 n
structure MatBox (𝕋 : Type) (m n : ℕ) where get : Mat 𝕋 m n

def materialiseVec {n : ℕ} (v : Vec 𝕋 n) : VecBox 𝕋 n :=
  let arr : Array 𝕋 := Array.ofFn v
  ⟨fun i => arr.getD i.val zero⟩

def materialiseMat {m n : ℕ} (M : Mat 𝕋 m n) : MatBox 𝕋 m n :=
  let arr : Array (Array 𝕋) := Array.ofFn fun i : Fin m => Array.ofFn fun j : Fin n => M i j
  ⟨fun i j => (arr.getD i.val #[]).getD j.val zero⟩

/-- `l.W` at `𝕋`, `n` columns rather than `l.inDim` (always the same count by
`MnistParse.aux_checkShape`), taken as the caller's own `n` so the recursion
below needs no cast; every caller reads it through `.get`. -/
def layerMat (instUnchecked : ExactDyadic → 𝕋) (l : MnistAffine) (n : ℕ) : MatBox 𝕋 l.outDim n :=
  materialiseMat fun i j => instUnchecked ((l.W.getD i.val #[]).getD j.val ExactDyadic.zero)

def layerVec (instUnchecked : ExactDyadic → 𝕋) (l : MnistAffine) : VecBox 𝕋 l.outDim :=
  materialiseVec fun i => instUnchecked (l.b.getD i.val ExactDyadic.zero)

/-- The dimension `buildChain`/`runLayers` reach after folding `layers`,
starting from `n`: every layer's own `outDim`, last one standing. -/
def finalDim : List MnistAffine → ℕ → ℕ
  | [], n => n
  | l :: rest, _ => finalDim rest l.outDim


/-! ## Building the network -/

/-- The network as a `NeuralNetwork`: `affineSoundLayer` per `Gemm`, the
library's own `ReluLayer` after every one but the last (`aux_checkShape`
already guarantees that). -/
def buildChain (instUnchecked : ExactDyadic → 𝕋) :
    (layers : List MnistAffine) → (n : ℕ) → NeuralNetwork S n (finalDim layers n)
  | [], _ => .output
  | l :: rest, n =>
    let aff : SoundLayer S n l.outDim := affineSoundLayer (layerMat instUnchecked l n).get
      (layerVec instUnchecked l).get
    if l.relu then
      .layer aff (.layer (⟨reluSlope, rfl⟩ : ReluLayer 𝕋 l.outDim l.outDim)
        (buildChain instUnchecked rest l.outDim))
    else
      .layer aff (buildChain instUnchecked rest l.outDim)


/-! ## Running it as a loop, with per-layer reporting

The same fold as `buildChain`, but as a loop rather than a `NeuralNetwork`
value, so a caller can read `S` back after each layer instead of only at the
end -- calling exactly the same `affineLayer.enclose`/`Layer.relu.enclose`
`buildChain` packs into `NeuralNetwork` nodes, so the two never disagree.

Run at `S := fun n => Interval (Vec 𝕋 n)`: a box carries no generators, so
`Mtimes`/`Relu` cost exactly `O(rows × cols)` per layer with nothing further
to bound. `Float.Zonotope` was tried first and dropped -- at these networks'
256-wide layers, its generator bookkeeping (`affineLayer`'s residual block,
`Relu`'s box-to-generator conversion, both `O(layer width)` *new* generators
every layer) made even one image impractically slow, order-reduction
(`Reduce.reduce`) included; nothing here is unsound at that representation
either, there is simply no reason to pay for it once a box suffices. -/

def runLayers (instUnchecked : ExactDyadic → 𝕋) :
    (layers : List MnistAffine) → {n : ℕ} → S n → S (finalDim layers n)
  | [], _, s => s
  | l :: rest, n, s =>
    -- one `Gemm`, then `Relu` unless this is the last layer
    let s1 : S l.outDim := (affineLayer (S := S) (layerMat instUnchecked l n).get
      (layerVec instUnchecked l).get).enclose s
    let s2 : S l.outDim := if l.relu then (Layer.relu (S := S) reluSlope).enclose s1 else s1
    runLayers instUnchecked rest s2

/-- `n`'s mean coordinatewise width `sup - inf`, `Output.lean`'s own "radius". -/
def meanRadius (toD : 𝕋 → Float) {n : ℕ} (I : Interval (Vec 𝕋 n)) : Float :=
  if n = 0 then 0.0 else
    ((Array.ofFn fun i : Fin n => toD (I.sup i) - toD (I.inf i)).foldl (· + ·) 0.0) / n.toFloat

/-- Whether a bound of `I` is past the type's range, `false` at a type without one. -/
def boxOverflows (overflows : Option (𝕋 → Bool)) {n : ℕ} (I : Interval (Vec 𝕋 n)) : Bool :=
  match overflows with
  | none => false
  | some f => (List.finRange n).any fun i => f (I.inf i) || f (I.sup i)

/-- `runLayers`, specialised at the box representation, reporting the mean width after every
completed layer beside the final box, and whether any layer's box held a value past the range. -/
def runReport (instUnchecked : ExactDyadic → 𝕋) (toD : 𝕋 → Float)
    (overflows : Option (𝕋 → Bool)) :
    (layers : List MnistAffine) → {n : ℕ} → Interval (Vec 𝕋 n) →
      Interval (Vec 𝕋 (finalDim layers n)) × Array Float × Bool
  | [], _, s => (s, #[], false)
  | l :: rest, n, s =>
    let s1 : Interval (Vec 𝕋 l.outDim) :=
      (affineLayer (S := fun n => Interval (Vec 𝕋 n)) (layerMat instUnchecked l n).get
        (layerVec instUnchecked l).get).enclose s
    let s2 : Interval (Vec 𝕋 l.outDim) :=
      if l.relu then (Layer.relu (S := fun n => Interval (Vec 𝕋 n)) reluSlope).enclose s1 else s1
    let (final, restRadii, restOver) := runReport instUnchecked toD overflows rest s2
    (final, #[meanRadius toD s2] ++ restRadii,
      boxOverflows overflows s1 || boxOverflows overflows s2 || restOver)


-- =======================================  MAIN THEOREM  ======================================= --

set_option linter.unusedSectionVars false in
/-- What `buildChain`'s enclosure is worth, restating `NeuralNetwork.enclose_outer`
at it alone: the exact network's value at every point of `X`. -/
theorem buildChain_sound (instUnchecked : ExactDyadic → 𝕋) (layers : List MnistAffine) (n : ℕ)
    (X : S n) {x : Vec ℝ n} (hx : x ∈ construct X) :
    (buildChain (S := S) instUnchecked layers n).eval.out x
      ∈ construct ((buildChain (S := S) instUnchecked layers n).enclose X) :=
  NeuralNetwork.enclose_outer _ X (Set.mem_image_of_mem _ hx)


/-! ## The input set: `k / 255` per pixel, a box -/

/-- `k`, the pixel byte, and `255`, read into `𝕋` unchecked -- both fit any
precision this harness runs at (`255 < 2^11`), so nothing is checked. -/
def pixelLo (instUnchecked : ExactDyadic → 𝕋) (k : ℕ) : 𝕋 :=
  divDown (instUnchecked ⟨(k : ℤ), 0⟩) (instUnchecked ⟨255, 0⟩)

def pixelHi (instUnchecked : ExactDyadic → 𝕋) (k : ℕ) : 𝕋 :=
  divUp (instUnchecked ⟨(k : ℤ), 0⟩) (instUnchecked ⟨255, 0⟩)

/-- `[divDown k 255, divUp k 255]` per pixel, both directed roundings of the
same ratio -- the tightest sound box `k / 255` fits in `𝕋`'s grid. -/
def inputBox (instUnchecked : ExactDyadic → 𝕋) (pixels : Array ℕ) :
    Interval (Vec 𝕋 pixels.size) where
  inf := fun i => pixelLo instUnchecked pixels[i]
  sup := fun i => pixelHi instUnchecked pixels[i]

/-- What `inputBox` is worth: it contains the exact point `k / 255` per
pixel, for any `instUnchecked` exact on the small integers `k` and `255`. -/
theorem inputBox_sound (instUnchecked : ExactDyadic → 𝕋)
    (hExact : ∀ d : ExactDyadic, toReal (instUnchecked d) = (d.mantissa : ℝ) * 2 ^ d.exponent)
    (pixels : Array ℕ) (x : Vec ℝ pixels.size)
    (hx : ∀ i, x i = (pixels[i]'i.isLt : ℝ) / 255) :
    x ∈ construct (inputBox instUnchecked pixels) := by -- --- PROOF ---
  intro i
  -- `k` and `255` read in exactly, both well inside any precision here
  have hk : toReal (instUnchecked (⟨(pixels[i] : ℤ), 0⟩ : ExactDyadic)) = (pixels[i] : ℝ) := by
    rw [hExact]; simp
  have hd : toReal (instUnchecked (⟨255, 0⟩ : ExactDyadic)) = (255 : ℝ) := by rw [hExact]; simp
  have h255 : (0 : ℝ) < toReal (instUnchecked (⟨255, 0⟩ : ExactDyadic)) := by rw [hd]; norm_num
  refine ⟨?_, ?_⟩
  · -- the lower bound rounds down from `k / 255`, so it never overshoots `x i`
    show toReal (divDown (instUnchecked ⟨(pixels[i] : ℤ), 0⟩) (instUnchecked ⟨255, 0⟩)) ≤ x i
    rw [hx i]
    calc toReal (divDown (instUnchecked ⟨(pixels[i] : ℤ), 0⟩) (instUnchecked ⟨255, 0⟩))
        ≤ toReal (instUnchecked (⟨(pixels[i] : ℤ), 0⟩ : ExactDyadic))
          / toReal (instUnchecked (⟨255, 0⟩ : ExactDyadic)) := divDown_le_div _ _ h255
      _ = (pixels[i] : ℝ) / 255 := by rw [hk, hd]
  · -- and the upper bound rounds up from the same ratio, so `x i` never exceeds it
    show x i ≤ toReal (divUp (instUnchecked ⟨(pixels[i] : ℤ), 0⟩) (instUnchecked ⟨255, 0⟩))
    rw [hx i]
    calc (pixels[i] : ℝ) / 255
        = toReal (instUnchecked (⟨(pixels[i] : ℤ), 0⟩ : ExactDyadic))
          / toReal (instUnchecked (⟨255, 0⟩ : ExactDyadic)) := by rw [hk, hd]
      _ ≤ toReal (divUp (instUnchecked ⟨(pixels[i] : ℤ), 0⟩) (instUnchecked ⟨255, 0⟩)) :=
          div_le_divUp _ _ h255

end CORALean.Bench.Mnist


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
