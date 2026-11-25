import CORALean.NN.Layers.Operations.Relu
import CORALean.NN.Layers.Operations.Sigmoid
import CORALean.NN.Layers.Operations.SigmoidRegression
import CORALean.NN.Layers.Operations.SigmoidRegressionExact
import CORALean.NN.Layers.Operations.TanhRegression
import CORALean.NN.Layers.Operations.TanhRegressionExact
import CORALean.NN.Layers.Operations.PolyBoxIndep
import CORALean.NN.Layers.Operations.SigmoidSingh
import CORALean.NN.Layers.Operations.TanhSingh
import CORALean.NN.Layers.Operations.Tanh
import CORALean.NN.Layers.Operations.LeakyRelu
import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Layers.Operations.Conv
import CORALean.NN.Layers.Operations.ElementwiseAffine
import CORALean.NN.Layers.Operations.BatchNorm
import CORALean.NN.Layers.Operations.ActivationPowers
import CORALean.NN.Layers.Operations.Activation
import CORALean.NN.Layers.Operations.SignRelaxation
import CORALean.NN.Layers.Operations.SquareChordTangentRelaxation
import CORALean.NN.Layers.Operations.ExpChordRelaxation
import CORALean.NN.Layers.Operations.ReciprocalRelaxation
import CORALean.NN.Layers.Operations.CubeRelaxation
import CORALean.NN.Layers.Operations.InverseRelaxation
import CORALean.NN.Layers.Operations.TrigRelaxation
import CORALean.NN.Layers.Operations.SoftplusLineRelaxation
import CORALean.NN.Layers.Operations.RootLineRelaxation
import CORALean.NN.Layers.Operations.InvSqrtRootLineRelaxation
import CORALean.NN.Layers.Operations.ProductLine
import CORALean.NN.Layers.Operations.SoftmaxSumBounds
import CORALean.NN.Layers.Operations.ReluRelaxation
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.NN.Layers.Theorems.ActivationPowersEncloses
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.PolyZonotope.Float.Instances
import CORALean.ContSet.Conversion.Float.Instances
import CORALean.Examples.Oracle.Ops.PolyZonotopeCodec
import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.Examples.Oracle.Ops.CrownOps
import CORALean.Examples.Oracle.Ops.GraphNetOps
import CORALean.Examples.Oracle.Ops.TaylmNetOps
import CORALean.Examples.Oracle.Ops.NnFormOps
import CORALean.Examples.Oracle.Ops.NnBoundsOps
import CORALean.Examples.Oracle.Ops.NnZonoBackpropOps
import CORALean.Examples.Oracle.Ops.NnInfoOps
import CORALean.Examples.Oracle.Ops.NnWeightOps
import CORALean.Examples.Oracle.Ops.NnRegionOps

/-!
# The network ops: CORA's `nnLayer` and `neuralNetwork` evaluation on a set

`nnLayer.evaluateZonotope` and `nnLayer.evaluatePolyZonotope` apply one layer to a zonotope or a
polynomial zonotope, `neuralNetwork.evaluate` a list of layers to either: `linear` (`W`, `b`),
`relu`, `leakyRelu` (`alpha`), `sigmoid` and `tanh` (`k`). `poly_method` is `singh` (CORA's
`'singh'`, the default), `regression` (CORA's `'regression'`, with a sound error) or `curvature`
(CORALean's tighter one). `regression_error` of `regression` is `bracket` (the default) or
`extremum` (CORA's exact error). `errorForm` of a polynomial zonotope is `box` (the default) or
`GI` (CORA's `add_approx_error_to_GI`). `poly`: order `k`, fit given. `conv` is ONNX's Conv at its
stencil; `relaxation`, `productLine`, `softmaxSumBounds` are CORA.cpp's lines. See oracle README.

## Inputs
* `dops` – dtype operations
* `name` – op name
* `req` – request
* `n` – dimension
* `X` – zonotope

## Output
* the names of the ops served, or the response fields of an op
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The relaxation of sigmoid and tanh the request asks for. -/
private inductive PolyMethod where
  | singh | curvature | regression | regressionExtremum
  deriving DecidableEq

/-- CORA.cpp's rounding margin of the square's band, `8 eps` of binary64, `2⁻⁴⁹` (exact). -/
private def aux_squareMargin : 𝕋 := FloatOps.half^[49] FloatOps.one

/-- CORA.cpp's rounding margin of the exponential's and the reciprocal's bands, `16 eps` of
binary64, `2⁻⁴⁸` (exact). -/
private def aux_bandMargin : 𝕋 := FloatOps.half^[48] FloatOps.one

/-- `2⁻ᵏ`, exact: CORA.cpp's `N eps` of binary64 for `N = 2⁵²⁻ᵏ` (`64 eps` the cube's margin,
`32 eps` the inverse's, `eps` and `4 eps` the trigonometric lines'). -/
private def aux_pow2 (k : ℕ) : 𝕋 := FloatOps.half^[k] FloatOps.one

/-- CORA.cpp's `kTiny`, `1e-300` in binary64, the least width its exponential's chord divides by:
the request's `tiny`, or that one (exact only at binary64). -/
private def aux_tiny (dops : DtypeOps 𝕋) (req : Json) : Except String 𝕋 := do
  let tj := (fieldOpt req "tiny").getD (Json.str "6032057205060441*2^-1049")
  dops.readExact "tiny" (← scalarField (Json.mkObj [("tiny", tj)]) "tiny")

/-- The natural numbers of the array `name` of `j`, exactly `len` of them, or `dflt` if absent. -/
private def aux_nats (j : Json) (name : String) (len : ℕ) (dflt : List ℕ) :
    Except String (List ℕ) := do
  match fieldOpt j name with
  | none => pure dflt
  | some _ =>
    let a ← arrField j name
    if a.size ≠ len then throw s!"conv: `{name}` needs {len} entries, not {a.size}"
    a.toList.mapM fun v => match v.getNat? with
      | .ok k => pure k
      | .error _ => throw s!"conv: `{name}` holds nonnegative integers"

/-- The convolution `layer` (CORA.cpp's `Layer::conv2d`) on a set of dimension `n`: `Layer.linear`
at the stencil matrix, `Layer.conv`'s `tapMat` with the taps on a pad dropped (they read zero), so
every entry is a stored weight or zero. -/
private def aux_convLayer (dops : DtypeOps 𝕋) {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
    [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]
    (layer : Json) (n : ℕ) (X : S n) : Except String (Σ m, S m) := do
  checkFields "conv" layer
    ["kind", "kernel", "kshape", "input", "stride", "dilation", "pads", "groups", "b"]
  -- the geometry
  let dims ← aux_nats layer "input" 3 []
  let ks ← aux_nats layer "kshape" 2 []
  let st ← aux_nats layer "stride" 2 [1, 1]
  let dl ← aux_nats layer "dilation" 2 [1, 1]
  let pd ← aux_nats layer "pads" 4 [0, 0, 0, 0]
  let groups := ((fieldOpt layer "groups").bind (·.getNat?.toOption)).getD 1
  let (C, H, Wd) := (dims.getD 0 0, dims.getD 1 0, dims.getD 2 0)
  let (kh, kw) := (ks.getD 0 0, ks.getD 1 0)
  let (sh, sw, dh, dw) := (st.getD 0 1, st.getD 1 1, dl.getD 0 1, dl.getD 1 1)
  let (pt, pl, pb, pr) := (pd.getD 0 0, pd.getD 1 0, pd.getD 2 0, pd.getD 3 0)
  if C * H * Wd ≠ n then throw s!"conv: the input {C}x{H}x{Wd} is not the set's dimension {n}"
  if groups = 0 ∨ C % groups ≠ 0 then throw s!"conv: `groups` {groups} must divide {C}"
  if sh = 0 ∨ sw = 0 ∨ dh = 0 ∨ dw = 0 ∨ kh = 0 ∨ kw = 0 then
    throw "conv: the kernel, the stride and the dilation must be positive"
  -- the kernel, the padded input and the output
  let cg := C / groups
  let k := cg * kh * kw
  let ⟨co, K⟩ ← parseMatColsFixed dops.readExact k (← field layer "kernel")
  if co % groups ≠ 0 then throw s!"conv: `groups` {groups} must divide the {co} outputs"
  if co = 0 then throw "conv: no outputs"
  let (Hp, Wp) := (H + pt + pb, Wd + pl + pr)
  let (eh, ew) := (dh * (kh - 1) + 1, dw * (kw - 1) + 1)
  if Hp < eh ∨ Wp < ew then throw "conv: the kernel is larger than the padded input"
  let (Ho, Wo) := ((Hp - eh) / sh + 1, (Wp - ew) / sw + 1)
  let m := co * Ho * Wo
  let b ← parseVecFixed dops.readExact m (← field layer "b")
  -- tap `l = (ci, ky, kx)` of output `j = (o, y, x)`: the input it reads, none on a pad
  let tap : ℕ → ℕ → Option ℕ := fun j l =>
    let (o, y, x) := (j / (Ho * Wo), j / Wo % Ho, j % Wo)
    let (ci, ky, kx) := (l / (kh * kw), l / kw % kh, l % kw)
    let (py, px) := (y * sh + ky * dh, x * sw + kx * dw)
    if pt ≤ py ∧ py < pt + H ∧ pl ≤ px ∧ px < pl + Wd then
      some (((o / (co / groups) * cg + ci) * H + (py - pt)) * Wd + (px - pl))
    else none
  -- the stencil: the weight of the first tap reading the input, else zero (`tapEntry`'s scan)
  let W : Mat 𝕋 m n := fun j i =>
    Fin.foldr k (fun l acc => if tap j.1 l.1 = some i.1 then
      (if h : j.1 / (Ho * Wo) < co then K ⟨_, h⟩ l else FloatOps.zero) else acc) FloatOps.zero
  pure ⟨m, (Layer.linear (S := S) W b).enclose X⟩

/-- The vector `name` of `layer`: one entry, or `k` of them, as `k` entries. -/
private def aux_perGroup (dops : DtypeOps 𝕋) (layer : Json) (name : String) (k : ℕ) :
    Except String (Vec 𝕋 k) := do
  let ⟨len, v⟩ ← parseVecDyn dops.readExact (← field layer name)
  if h : len = 1 then pure fun _ => v ⟨0, by omega⟩
  else if h' : len = k then pure fun i => v ⟨i.1, by omega⟩
  else throw s!"`{name}` needs one entry or {k}, not {len}"

/-- The average pool `layer` (CORA.cpp's `Layer::avg_pool2d`): the depthwise convolution of the
window's ones times `1 / (pool area)` (rounded up), the stride the pool's unless given, no bias. -/
private def aux_avgPoolLayer (dops : DtypeOps 𝕋) {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
    [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]
    (layer : Json) (n : ℕ) (X : S n) : Except String (Σ m, S m) := do
  checkFields "avgPool" layer ["kind", "pool", "input", "stride", "pads"]
  let dims ← aux_nats layer "input" 3 []
  let pool ← aux_nats layer "pool" 2 []
  let st ← aux_nats layer "stride" 2 pool
  let (C, kh, kw) := (dims.getD 0 0, pool.getD 0 0, pool.getD 1 0)
  if kh = 0 ∨ kw = 0 then throw "avgPool: the pool must be positive"
  let areaJ := Json.mkObj [("pool", Json.str s!"{kh * kw}*2^0")]
  let area ← dops.readExact "pool" (← scalarField areaJ "pool")
  let winv := FloatOps.divUp FloatOps.one area
  -- the kernel, one row per channel
  let kernel := Json.mkObj [("rows", Lean.toJson C), ("cols", Lean.toJson (kh * kw)),
    ("data", Json.arr ((List.replicate (C * kh * kw) (Json.str (dops.showExact winv))).toArray))]
  let pads := (fieldOpt layer "pads").getD (Lean.toJson [0, 0, 0, 0])
  -- the output size, from the geometry, for the bias of zeros
  let pd ← aux_nats layer "pads" 4 [0, 0, 0, 0]
  let (H, Wd) := (dims.getD 1 0, dims.getD 2 0)
  let (sh, sw) := (st.getD 0 1, st.getD 1 1)
  if sh = 0 ∨ sw = 0 then throw "avgPool: the stride must be positive"
  let (Hp, Wp) := (H + pd.getD 0 0 + pd.getD 2 0, Wd + pd.getD 1 0 + pd.getD 3 0)
  if Hp < kh ∨ Wp < kw then throw "avgPool: the pool is larger than the padded input"
  let m := C * ((Hp - kh) / sh + 1) * ((Wp - kw) / sw + 1)
  let b := Json.mkObj [("rows", Lean.toJson m), ("cols", Lean.toJson 1),
    ("data", Json.arr ((List.replicate m (Json.str "0*2^0")).toArray))]
  aux_convLayer dops (Json.mkObj [("kind", Json.str "conv"), ("kernel", kernel),
    ("kshape", Lean.toJson [kh, kw]), ("input", ← field layer "input"),
    ("stride", Lean.toJson [sh, sw]), ("pads", pads), ("groups", Lean.toJson C), ("b", b)]) n X

/-- `2ᵏ⁻¹` from below by doublings, the bound `expUp k` asks of its argument. -/
private def aux_expBound (k : ℕ) : 𝕋 := (fun x => FloatOps.addDown x x)^[k - 1] FloatOps.one

/-- CORA.cpp's line of the activation `kind` (exp, reciprocal, cube, inverse, softplus, root or
invSqrt) as a layer, after a check of the domain its theorem asks of the boxes `[lo, hi]`. -/
private def aux_lineRelaxation (dops : DtypeOps 𝕋) (method : PolyMethod) (layer : Json)
    (kind : String) {n : ℕ} (lo hi : Vec 𝕋 n) : Except String (Relaxation 𝕋) := do
  if method = .curvature then throw s!"{kind}: the poly_method curvature has no line of `{kind}`"
  -- CORA.cpp's evaluate: the least-squares slope for `regression`, Singh's otherwise
  let regression := method = .regression ∨ method = .regressionExtremum
  let below (B : 𝕋) := (List.finRange n).all fun i => FloatOps.le (hi i) B
  let atLeastZero := (List.finRange n).all fun i => FloatOps.le FloatOps.zero (lo i)
  let aboveZero := (List.finRange n).all fun i => FloatOps.ltStrict FloatOps.zero (lo i)
  match kind with
  | "exp" =>
    checkFields "exp" layer ["kind", "k", "p", "tiny"]
    let k ← natField layer "k"
    let p ← natField layer "p"
    let τ ← aux_tiny dops layer
    if !below (aux_expBound k) then throw "exp: every neuron's `u` must be at most 2^k / 2"
    pure (expChordRelaxation k p τ aux_bandMargin)
  -- the chord bands at CORA.cpp's margins
  | "reciprocal" =>
    checkFields "reciprocal" layer ["kind", "p"]
    pure (reciprocalRelaxation (← natField layer "p") aux_bandMargin)
  | "cube" =>
    checkFields "cube" layer ["kind", "p"]
    pure (cubeRelaxation (← natField layer "p") (aux_pow2 46))
  | "inverse" =>
    checkFields "inverse" layer ["kind", "p"]
    if !aboveZero then throw "inverse: every neuron's `l` must be above zero"
    pure (inverseRelaxation (← natField layer "p") (aux_pow2 47))
  -- the monotone lines, at no margin
  | "softplus" =>
    checkFields "softplus" layer ["kind", "k", "p"]
    let k ← natField layer "k"
    if !below (aux_expBound k) then throw "softplus: every neuron's `u` must be at most 2^k / 2"
    pure (softplusLineRelaxation regression k (← natField layer "p"))
  | "root" =>
    checkFields "root" layer ["kind", "p"]
    if !atLeastZero then throw "root: every neuron's `l` must be at least zero"
    pure (rootLineRelaxation regression (← natField layer "p"))
  | _ =>
    checkFields "invSqrt" layer ["kind", "k", "p"]
    if !aboveZero then throw "invSqrt: every neuron's `l` must be above zero"
    pure (invSqrtRootLineRelaxation regression (← natField layer "k") (← natField layer "p"))

/-- One layer of the request on a set of the family `S`, of dimension `n`; the set of the new
dimension. `method` picks the relaxation for sigmoid and tanh. -/
private def aux_runLayer (dops : DtypeOps 𝕋) {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
    [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]
    (method : PolyMethod) (layer : Json) (s : Σ n, S n) : Except String (Σ n, S n) := do
  let ⟨n, X⟩ := s
  -- the layer by its kind, its weights read at the scalar of the dtype
  match ← strField layer "kind" with
  | "linear" =>
    checkFields "linear" layer ["kind", "W", "b"]
    let ⟨m, W⟩ ← parseMatColsFixed dops.readExact n (← field layer "W")
    let b ← parseVecFixed dops.readExact m (← field layer "b")
    pure ⟨m, (Layer.linear (S := S) W b).enclose X⟩
  | "relu" =>
    checkFields "relu" layer ["kind"]
    pure ⟨n, (Layer.relu (S := S) (n := n)).enclose X⟩
  | "leakyRelu" =>
    checkFields "leakyRelu" layer ["kind", "alpha"]
    let α ← dops.readExact "alpha" (← scalarField layer "alpha")
    pure ⟨n, (Layer.leakyRelu (S := S) (n := n) α).enclose X⟩
  -- the two with the choice of the relaxation
  | "sigmoid" =>
    checkFields "sigmoid" layer ["kind", "k"]
    let k ← natField layer "k"
    pure ⟨n, (match method with
      | .curvature => (Layer.sigmoid (S := S) (n := n) k).enclose X
      | .singh => (Layer.sigmoidSingh (S := S) (n := n) k).enclose X
      | .regression => (Layer.sigmoidRegression (S := S) (n := n) k).enclose X
      | .regressionExtremum => (Layer.sigmoidRegressionExact (S := S) (n := n) k).enclose X)⟩
  | "tanh" =>
    checkFields "tanh" layer ["kind", "k"]
    let k ← natField layer "k"
    pure ⟨n, (match method with
      | .curvature => (Layer.tanh (S := S) (n := n) k).enclose X
      | .singh => (Layer.tanhSingh (S := S) (n := n) k).enclose X
      | .regression => (Layer.tanhRegression (S := S) (n := n) k).enclose X
      | .regressionExtremum => (Layer.tanhRegressionExact (S := S) (n := n) k).enclose X)⟩
  -- CORA.cpp's layers without a CORA counterpart: the sign and the square's chord-tangent band
  | "sign" =>
    checkFields "sign" layer ["kind"]
    pure ⟨n, (Layer.activation (S := S) (n := n) signRelaxation).enclose X⟩
  | "square" =>
    checkFields "square" layer ["kind"]
    pure ⟨n, (Layer.activation (S := S) (n := n)
      (squareChordTangentRelaxation aux_squareMargin)).enclose X⟩
  -- CORA.cpp's lines of the activations it adds, a softmax's exp and reciprocal among them
  | "exp" | "reciprocal" | "cube" | "inverse" | "softplus" | "root" | "invSqrt" =>
    let J := IntervalOuter.interval X
    let R ← aux_lineRelaxation dops method layer (← strField layer "kind") J.inf J.sup
    pure ⟨n, (Layer.activation (S := S) (n := n) R).enclose X⟩
  | "conv" => aux_convLayer dops layer n X
  -- the linear layers of CORA.cpp's port, each as the map CORA.cpp folds it to
  | "elementwiseAffine" =>
    checkFields "elementwiseAffine" layer ["kind", "scale", "offset"]
    let scale ← aux_perGroup dops layer "scale" n
    let offset ← aux_perGroup dops layer "offset" n
    pure ⟨n, (Layer.elementwiseAffine (S := S) scale offset).enclose X⟩
  | "batchNorm" =>
    checkFields "batchNorm" layer ["kind", "scale", "offset", "mean", "var", "epsilon", "input",
      "p"]
    let dims ← aux_nats layer "input" 3 []
    let (C, px) := (dims.getD 0 0, dims.getD 1 0 * dims.getD 2 0)
    if C * px ≠ n then throw s!"batchNorm: the input {dims} is not the set's dimension {n}"
    if hC0 : C = 0 then throw "batchNorm: no channels" else
      let p ← natField layer "p"
      let ε ← dops.readExact "epsilon" (← scalarField layer "epsilon")
      let scale ← aux_perGroup dops layer "scale" C
      let offset ← aux_perGroup dops layer "offset" C
      let mean ← aux_perGroup dops layer "mean" C
      let var ← aux_perGroup dops layer "var" C
      -- CORA.cpp's fold: factor = scale / sqrt(var + epsilon), bias = offset - mean factor
      let factor : Vec 𝕋 C := fun c =>
        FloatOps.divUp (scale c) (sqrtUp p (FloatOps.addUp (var c) ε))
      let bias : Vec 𝕋 C := fun c => subUp (offset c) (FloatOps.mulUp (mean c) (factor c))
      have hC : 0 < C := Nat.pos_of_ne_zero hC0
      let chan : Fin n → Fin C := fun i =>
        ⟨min (i.1 / px) (C - 1), lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hC Nat.one_pos)⟩
      pure ⟨n, (Layer.batchNorm (S := S) chan factor bias).enclose X⟩
  | "avgPool" => aux_avgPoolLayer dops layer n X
  | "lipLinear" =>
    checkFields "lipLinear" layer ["kind", "W", "b", "lambda"]
    let ⟨m, W⟩ ← parseMatColsFixed dops.readExact n (← field layer "W")
    let b ← parseVecFixed dops.readExact m (← field layer "b")
    let lam ← dops.readExact "lambda" (← scalarField layer "lambda")
    -- CORA.cpp's rows scaled by max(1, |W_i| 1 / lambda), each entry divided by it
    let norm : Vec 𝕋 m := fun i =>
      FloatOps.maximum (FloatOps.divUp (sumUp fun j => absolute (W i j)) lam) FloatOps.one
    pure ⟨m, (Layer.linear (S := S) (fun i j => FloatOps.divUp (W i j) (norm i))
      fun i => FloatOps.divUp (b i) (norm i)).enclose X⟩
  | k => throw s!"a layer's `kind` must be linear, conv, relu, leakyRelu, sigmoid, tanh, sign, \
      square, exp, reciprocal, cube, inverse, softplus, root, invSqrt, elementwiseAffine, \
      batchNorm, avgPool or lipLinear, not `{k}` (`poly` only as the one layer of \
      `nnLayer.evaluatePolyZonotope`)"

/-- The layer `poly` on the polynomial zonotope: the fits `coeffs` (a row per neuron) and their
errors `d` as a relaxation that does not depend on the box. -/
private def aux_runPowers (dops : DtypeOps 𝕋) (layer : Json) (n : ℕ) (X : 𝒫𝒵[𝕋] n) :
    Except String (𝒫𝒵[𝕋] n) := do
  checkFields "poly" layer ["kind", "coeffs", "d"]
  let ⟨K, C⟩ ← parseMatRowsFixed dops.readExact n (← field layer "coeffs")
  let d ← parseVecFixed dops.readExact n (← field layer "d")
  if hK : K = 0 then throw "poly: `coeffs` needs at least one column"
  else
    let P : LayerRelaxation 𝕋 n (K - 1) :=
      fun i => ⟨fun _ _ k => C i ⟨k, by omega⟩, fun _ _ => d i⟩
    pure ((Layer.activationPowers P).enclose X)

/-- The relaxation of `kind` at every neuron's box `[l i, u i]`: sign, square, the chord bands, the
monotone lines (softplus, root, invSqrt), sin, cos, or relu (CORALean's slope, or `alpha i` where
the neuron crosses zero); the kinds and their fields are in the oracle README. -/
private def aux_relaxation (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "relaxation" req ["kind", "l", "u", "alpha", "k", "p", "tiny", "method"]
  let ⟨n, l⟩ ← parseVecDyn dops.readExact (← field req "l")
  let u ← parseVecFixed dops.readExact n (← field req "u")
  let kind ← strField req "kind"
  if kind ≠ "relu" ∧ (fieldOpt req "alpha").isSome then
    throw s!"relaxation: `alpha` is for `relu`, not `{kind}`"
  if kind ≠ "exp" ∧ (fieldOpt req "tiny").isSome then
    throw s!"relaxation: `tiny` is for `exp`, not `{kind}`"
  if kind ∉ ["exp", "sin", "cos", "softplus", "invSqrt"] ∧ (fieldOpt req "k").isSome then
    throw s!"relaxation: `k` is for `exp`, `sin`, `cos`, `softplus` and `invSqrt`, not `{kind}`"
  if kind ∉ ["exp", "reciprocal", "cube", "inverse", "softplus", "root", "invSqrt"] ∧
      (fieldOpt req "p").isSome then
    throw s!"relaxation: `p` is for `exp`, `reciprocal`, `cube`, `inverse`, `softplus`, `root` \
      and `invSqrt`, not `{kind}`"
  if kind ∉ ["softplus", "root", "invSqrt"] ∧ (fieldOpt req "method").isSome then
    throw s!"relaxation: `method` is for `softplus`, `root` and `invSqrt`, not `{kind}`"
  -- CORA.cpp's `priv_monotone_line`: the least-squares slope (the default) or Singh's
  let regression ← match fieldOpt req "method" with
    | none => pure true
    | some _ => match ← strField req "method" with
      | "regression" => pure true
      | "singh" => pure false
      | m => throw s!"relaxation: `method` must be singh or regression, not `{m}`"
  -- one relaxation per neuron: the ReLU's slope may differ from neuron to neuron
  let R : Fin n → Relaxation 𝕋 ← match kind with
    | "sign" => pure fun _ => signRelaxation
    | "square" => pure fun _ => squareChordTangentRelaxation aux_squareMargin
    | "exp" => do
      let k ← natField req "k"
      let p ← natField req "p"
      let τ ← aux_tiny dops req
      pure fun _ => expChordRelaxation k p τ aux_bandMargin
    | "reciprocal" => do
      let p ← natField req "p"
      pure fun _ => reciprocalRelaxation p aux_bandMargin
    | "cube" => do
      let p ← natField req "p"
      pure fun _ => cubeRelaxation p (aux_pow2 46)
    | "inverse" => do
      let p ← natField req "p"
      -- CORA.cpp's line exists for `0 < l` only (`kOutOfRangeMessage` otherwise)
      if (List.finRange n).any fun i => !FloatOps.ltStrict FloatOps.zero (l i) then
        throw "relaxation: `inverse` needs every `l` above zero"
      pure fun _ => inverseRelaxation p (aux_pow2 47)
    | "softplus" => do
      let k ← natField req "k"
      let p ← natField req "p"
      pure fun _ => softplusLineRelaxation regression k p
    | "root" => do
      let p ← natField req "p"
      -- CORA.cpp's line exists for `0 <= l` only (`out_of_domain` otherwise)
      if (List.finRange n).any fun i => !FloatOps.le FloatOps.zero (l i) then
        throw "relaxation: `root` needs every `l` at least zero"
      pure fun _ => rootLineRelaxation regression p
    | "invSqrt" => do
      let k ← natField req "k"
      let p ← natField req "p"
      -- CORA.cpp's line exists for `0 < l` only (`out_of_domain` otherwise)
      if (List.finRange n).any fun i => !FloatOps.ltStrict FloatOps.zero (l i) then
        throw "relaxation: `invSqrt` needs every `l` above zero"
      pure fun _ => invSqrtRootLineRelaxation regression k p
    | "sin" | "cos" => do
      let k ← natField req "k"
      pure fun _ => trigRelaxation (kind == "cos") k (aux_pow2 48) (aux_pow2 52) (aux_pow2 50)
    | "relu" => match fieldOpt req "alpha" with
      | none => pure fun _ => reluRelaxation reluSlope
      | some aj => do
        let a ← parseVecFixed dops.readExact n aj
        -- the stable neurons keep CORALean's exact slope, the crossing ones take `alpha`
        pure fun i => reluRelaxation fun lo hi =>
          if FloatOps.le hi FloatOps.zero then FloatOps.zero
          else if FloatOps.le FloatOps.zero lo then FloatOps.one else a i
    | k => throw s!"relaxation: `kind` must be sign, square, exp, reciprocal, cube, inverse, \
      softplus, root, invSqrt, sin, cos or relu, not `{k}`"
  pure [("slope", printVec dops.showExact fun i => (R i).slope (l i) (u i)),
    ("offset", printVec dops.showExact fun i => (R i).offset (l i) (u i)),
    ("error", printVec dops.showExact fun i => (R i).error (l i) (u i))]

/-- `N * 2⁻⁵²`, CORA.cpp's `N eps` of binary64 (exact for `N < 2⁵³`). -/
private def aux_epsTimes (dops : DtypeOps 𝕋) (N : ℕ) : Except String 𝕋 := do
  dops.readExact "eps" (← scalarField (Json.mkObj [("eps", Json.str s!"{N}*2^-52")]) "eps")

/-- `nnLayer.productLine`: the lines of `a_i b_i`, `a` the first `n` rows of `Z` and `b` the rest,
with the interval center's radii `dr` (none: zero; `E` is not read), at CORA.cpp's margins. -/
private def aux_productLine (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "productLine" req ["Z", "dr", "p", "tiny"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let p ← natField req "p"
  let τ ← aux_tiny dops req
  let m := dz.n
  if m % 2 ≠ 0 then throw s!"productLine: `Z` needs an even dimension, not {m}"
  let n := m / 2
  let dr : Vec 𝕋 m ← match fieldOpt req "dr" with
    | none => pure fun _ => FloatOps.zero
    | some j => parseVecFixed dops.readExact m j
  let q := dz.Z.h
  let w₁ ← aux_epsTimes dops (2 * (q + 2) + 16)
  let w₂ := aux_bandMargin (𝕋 := 𝕋)
  if hm : 0 < m then
    -- coordinate `i` of `a` is row `i`, of `b` row `n + i`
    let row : ℕ → Fin m := fun i => ⟨i % m, Nat.mod_lt _ hm⟩
    let line : Fin n → 𝕋 × 𝕋 := fun i =>
      let (a, b) := (row i.1, row (n + i.1))
      productLine p τ w₁ w₂ (dz.Z.c a) (dz.Z.c b) (fun j => dz.Z.G j a) (fun j => dz.Z.G j b)
        (dr a) (dr b)
    pure [("slope", printVec dops.showExact fun k : Fin m =>
        if k.1 < n then dz.Z.c (row (n + k.1)) else dz.Z.c (row (k.1 - n))),
      ("offset", printVec dops.showExact fun i => (line i).1),
      ("error", printVec dops.showExact fun i => (line i).2)]
  else throw "productLine: `Z` has no rows"

/-- `nnLayer.softmaxSumBounds`: the box of `W e + b` for the exponentials `e` of `[l, u]`, at
CORA.cpp's margin `(n + 4) eps`. -/
private def aux_softmaxSumBounds (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "softmaxSumBounds" req ["W", "b", "l", "u", "k"]
  let ⟨n, l⟩ ← parseVecDyn dops.readExact (← field req "l")
  let u ← parseVecFixed dops.readExact n (← field req "u")
  let ⟨m, W⟩ ← parseMatColsFixed dops.readExact n (← field req "W")
  let b ← parseVecFixed dops.readExact m (← field req "b")
  let k ← natField req "k"
  let I := softmaxSumBounds k (← aux_epsTimes dops (n + 4)) W b l u
  pure [("inf", printVec dops.showExact I.inf), ("sup", printVec dops.showExact I.sup)]

/-- The layers of the list, in order, on the set. -/
private def aux_runLayers (dops : DtypeOps 𝕋) {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
    [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]
    (method : PolyMethod) (layers : List Json) (s : Σ n, S n) : Except String (Σ n, S n) :=
  layers.foldlM (fun s l => aux_runLayer dops method l s) s

/-- The layers on a polynomial zonotope; with `gi`, CORA's `add_approx_error_to_GI`: the box of a
layer goes to the independent generators. -/
private def aux_runPoly (dops : DtypeOps 𝕋) (method : PolyMethod) (gi : Bool) (layers : List Json)
    (s : Σ n, 𝒫𝒵[𝕋] n) : Except String (Σ n, 𝒫𝒵[𝕋] n) :=
  if gi then
    letI : OfInterval 𝒫𝒵[𝕋] 𝕋 := OfInterval.polyIndep
    aux_runLayers dops (S := 𝒫𝒵[𝕋]) method layers s
  else aux_runLayers dops (S := 𝒫𝒵[𝕋]) method layers s

/-- The layers on the zonotope `Z` or the polynomial zonotope `P` of the request, the output set
under the same key. `gi` puts the error of a layer into the independent generators of `P`. -/
private def aux_run (dops : DtypeOps 𝕋) (name : String) (req : Json) (method : PolyMethod)
    (gi : Bool) (layers : List Json) : Resp := do
  match fieldOpt req "Z", fieldOpt req "P" with
  | some zj, none =>
    if fieldOpt req "errorForm" |>.isSome then
      throw s!"{name}: `errorForm` is for a polynomial zonotope, a zonotope has no error box"
    let dz ← parseZonotope dops.readExact zj
    let ⟨_, Y⟩ ← aux_runLayers dops (S := 𝒵[𝕋]) method layers ⟨dz.n, dz.Z⟩
    pure [("Z", printZonotope dops.showExact Y)]
  | none, some pj =>
    let ⟨n, _⟩ ← parseVecDyn dops.readExact (← field pj "c")
    let P ← parsePolyZonotopeFixed dops.readExact n pj
    let ⟨_, Y⟩ ← aux_runPoly dops method gi layers ⟨n, P⟩
    pure [("P", printPolyZonotope dops.showExact Y)]
  | _, _ => throw s!"{name}: needs exactly one of `Z` (a zonotope) and `P` (a polynomial zonotope)"

/-- The `poly_method`: `singh` (or none), `curvature` or `regression`, the last with its
`regression_error`: `bracket` (or none) or `extremum`, which only `regression` takes. -/
private def aux_method (name : String) (req : Json) : Except String PolyMethod := do
  let err := (fieldOpt req "regression_error").bind (·.getStr?.toOption)
  if (fieldOpt req "regression_error").isSome && err.isNone then
    throw s!"{name}: `regression_error` must be a string"
  match (fieldOpt req "poly_method").bind (·.getStr?.toOption), err with
  | some "regression", none | some "regression", some "bracket" => pure .regression
  | some "regression", some "extremum" => pure .regressionExtremum
  | some "regression", some e =>
    throw s!"{name}: `regression_error` must be bracket or extremum, not `{e}`"
  | _, some _ => throw s!"{name}: `regression_error` is for `poly_method` regression"
  | none, none | some "singh", none => pure .singh
  | some "curvature", none => pure .curvature
  | some m, none =>
    throw s!"{name}: `poly_method` must be singh, regression or curvature, not `{m}`"

/-- The `errorForm`: `true` for `GI`, `false` for `box` or none. -/
private def aux_errorForm (name : String) (req : Json) : Except String Bool :=
  match (fieldOpt req "errorForm").bind (·.getStr?.toOption) with
  | none | some "box" => pure false
  | some "GI" => pure true
  | some m => throw s!"{name}: `errorForm` must be box or GI, not `{m}`"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layers of the request's `layers`, at its `poly_method`, on the zonotope `X`: the network's
image, of whatever dimension the last layer gives. -/
def networkOnZonotope (dops : DtypeOps 𝕋) (name : String) (req : Json) (n : ℕ)
    (X : Zonotope (Vec 𝕋 n)) : Except String (Σ k, Zonotope (Vec 𝕋 k)) := do
  aux_runLayers dops (S := 𝒵[𝕋]) (← aux_method name req) (← arrField req "layers").toList ⟨n, X⟩

/-- Every op of `nnLayer.`, without the prefix. -/
def nnLayerOpNames : List String :=
  [ "evaluateZonotope", "evaluatePolyZonotope", "relaxation", "productLine", "softmaxSumBounds" ] ++
    nnFormLayerOpNames ++ [ "backpropZonotopeBatch" ] ++ nnRegionOpNames

/-- Every op of `neuralNetwork.`, without the prefix. -/
def neuralNetworkOpNames : List String :=
  [ "evaluate", "backwardBound", "evaluateGraph", "evaluateTaylm", "normalForm",
    "propagateBounds", "backpropIntervalBatch", "backprop", "sensitivity", "backpropZonotopeBatch",
    "computeFGSMAttack", "getInputNeuronOrder" ] ++ nnInfoOpNames ++ nnWeightOpNames

/-- `op` of `nnLayer.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleNnLayerOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "relaxation" => some (aux_relaxation dops req)
  | "productLine" => some (aux_productLine dops req)
  | "softmaxSumBounds" => some (aux_softmaxSumBounds dops req)
  | "evaluateZonotope" | "evaluatePolyZonotope" => some (do
    checkFields op req ["layer", "Z", "P", "poly_method", "regression_error", "errorForm"]
    let layer ← field req "layer"
    if (← strField layer "kind") = "poly" then
      -- order `k` with the fit given: a polynomial zonotope, the error in `GI`
      if op ≠ "evaluatePolyZonotope" then throw s!"{op}: the layer `poly` needs `P`"
      if (← aux_errorForm op req) = false ∧ (fieldOpt req "errorForm").isSome then
        throw s!"{op}: the layer `poly` puts its error in `GI`"
      let pj ← field req "P"
      let ⟨n, _⟩ ← parseVecDyn dops.readExact (← field pj "c")
      let X ← parsePolyZonotopeFixed dops.readExact n pj
      let ids ← parsePolyZonotopeIds X pj
      pure [("P", printPolyZonotopeIds dops.showExact (← aux_runPowers dops layer n X).materialise
        ids)]
    else
      aux_run dops op req (← aux_method op req) (← aux_errorForm op req) [layer])
  | "backpropZonotopeBatch" => some (backpropZonotopeBatchLayerOp dops req)
  | _ => (handleNnFormLayerOp dops op req).orElse fun _ => handleNnRegionOp dops op req

/-- `op` of `neuralNetwork.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleNeuralNetworkOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "evaluate" => some (do
    checkFields op req ["layers", "Z", "P", "poly_method", "regression_error", "errorForm"]
    aux_run dops op req (← aux_method op req) (← aux_errorForm op req)
      (← arrField req "layers").toList)
  | "backwardBound" => some (crownBackwardBoundOp dops req)
  | "evaluateGraph" => some (evaluateGraphOp dops req)
  | "evaluateTaylm" => some (evaluateTaylmOp dops req)
  | "normalForm" => some (normalFormOp dops req)
  | "propagateBounds" => some (propagateBoundsOp dops req)
  | "backpropIntervalBatch" => some (backpropOp dops false req)
  | "backprop" => some (backpropOp dops true req)
  | "sensitivity" => some (sensitivityOp dops req)
  | "backpropZonotopeBatch" => some (backpropZonotopeBatchOp dops req)
  | "computeFGSMAttack" => some (fgsmAttackOp dops req)
  | "getInputNeuronOrder" => some (inputNeuronOrderOp dops req)
  | _ => (handleNnInfoOp op req).orElse fun _ => handleNnWeightOp dops op req

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
