# Fully Automatic Neural Network Reduction for Formal Verification

```bibtex
@article{ladner2025fully,
  author = {Ladner, T. and Althoff, M.},
  title = {Fully Automatic Neural Network Reduction for Formal Verification},
  journal = {Transactions on Machine Learning Research},
  year = {2025}
}
```

**Source:** https://arxiv.org/pdf/2305.01932v3  
**Inventory:** confirmed

Reducing a network before verifying it, and the guarantee that the reduced
network's output encloses the original's — `NN.Definitions.Reduction` and the merge
buckets under it, and the paper's three algorithms: `bucketTolerance`,
`reduceOnTheFly` and `compressionPreprocessing` in `NN.Operations`, each written
once over the scalar, so the same definition runs at a machine one.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (§2) feed-forward neural network as alternating linear/nonlinear layers, h0=x, h_k=L_k(h_{k-1}) | n/a — a preliminary restated from the literature, not a result of this paper | `restated` |
| `Def. 2` | (§2) zonotope with center c and generator matrix G, Z = ⟨c,G⟩_Z [cites Girard 2005, Def. 1] | n/a — restated from Girard 2005, which this formalization does not draw on directly | `restated` |
| `Def. 3` | (§2/§3) merge bucket: set of neuron indices in a nonlinear layer whose output bounds lie within tolerance δ of value y | [`IsInMergeBucket.lean`](../../src/CORALean/NN/Definitions/IsInMergeBucket.lean) | `correct` |
| `Eq. 2` | (§3.1) linear layers adapted to carry the approximation error: `L̂_k(h_{k-1}) = W_k h_{k-1} + b_k ⊕ I'_k` if layer k is linear, `ϕ_k(h_{k-1})` otherwise, where `I'_k` is initialized with `[0, 0] ⊂ ℝ^{n_k}` | [`ReducibleNetwork.lean`](../../src/CORALean/NN/Definitions/ReducibleNetwork.lean), [`ReducedLinearToLayer.lean`](../../src/CORALean/NN/Operations/ReducedLinearToLayer.lean), [`ReducibleNetworkToNetwork.lean`](../../src/CORALean/NN/Operations/ReducibleNetworkToNetwork.lean), [`LinearWithErrorZero.lean`](../../src/CORALean/NN/Theorems/Real/LinearWithErrorZero.lean) — `ReducedLinear` is the linear case `(W, b, I')`, stored in any scalar, laid out as `Layer.linearWithError` by `toLayer`, and `ReducibleNetwork` is Def. 1 two layers at a time in this form, which is what Alg. 2 reads and writes. `Real.Layer.linearWithError_zero` is the initialization: at `I' = [0, 0]` the layer *is* Def. 1's, at ℝ, where the box's sum is exact. See the Findings. | `correct` |
| `Eq. 3` | multiple disjoint merge buckets for a layer, B_{k,δ} = {B_{k,y1,δ}, B_{k,y2,δ}, ...} | n/a — the paper setting up its own notation for the buckets Eq. 4 sums errors over, not a claim to formalize | `not-a-claim` |
| `Eq. 4` | overall approximation error under multiple disjoint merge buckets is the Minkowski sum of individual Prop. 4 errors, simplifying to a single weighted-interval term | [`MergeErrorSplit.lean`](../../src/CORALean/NN/Theorems/MergeErrorSplit.lean) | `correct` |
| `Eq. 5` | (§3.2) static merge buckets, determined by the asymptotic values of ϕ_k: `{B_{k,0,δ}, B_{k,1,δ}}` for sigmoid, `{B_{k,-1,δ}, B_{k,1,δ}}` for tanh, `{B_{k,0,δ}}` for ReLU | [`InitMergeBuckets.lean`](../../src/CORALean/NN/Operations/InitMergeBuckets.lean) — `step_staticMergeBuckets` at the values a layer stores in `MergeBuckets.static`. Which values go with which ϕ_k is the caller's to supply, not read off the activation: a `Relaxation` names no asymptote. A neuron several buckets hold (δ ≥ 1/2 for sigmoid) is merged once, so the buckets stay disjoint as Eq. 4 assumes | `correct` |
| `Eq. 6` | (§3.2) dynamic merge buckets at the center of each neuron's bounds, `B_{k,δ} = {B_{k,c(i),δ} \| c = (l_k+u_k)/2, i ∈ [n_k]}`, ensured disjoint and only used if they contain multiple neurons | [`InitMergeBuckets.lean`](../../src/CORALean/NN/Operations/InitMergeBuckets.lean) — `step_dynamicMergeBuckets`. [1] does not say how disjointness is ensured: here the centers are taken in neuron order, each bucket skipping the neurons an earlier one took, and a bucket is used only if it then holds two or more | `underspecified` — does not say how disjointness of the dynamic buckets is ensured |
| `Alg. 1` | (§3.3) Automatic Determination of Bucket Tolerance: from bounds `I_k = [l_k, u_k]` and a reduction rate ρ, `δ_min ← 0`, `δ_max ← max(u_k) − min(l_k)`. Grow `δ_max ← 10 δ_max` while `n̂_k/n_k > ρ`, with `n̂_k = n_k − Σ_{B ∈ B_{k,δ}} \|B\|`; then bisect, `δ ← (δ_min + δ_max)/2`, `δ_max ← δ` if `n̂_k < ρ n_k` (too many merged) and `δ_min ← δ` otherwise, while `n̂_k/n_k ≉ ρ`; return `B_{k,δ}` | [`BucketTolerance.lean`](../../src/CORALean/NN/Operations/BucketTolerance.lean), [`BucketToleranceApprox.lean`](../../src/CORALean/NN/Theorems/BucketToleranceApprox.lean), [`BucketToleranceNone.lean`](../../src/CORALean/NN/Theorems/Real/BucketToleranceNone.lean) — `bucketTolerance`, one `let` per line, written once over the scalar, and `bucketTolerance_approx`: the buckets returned leave `n̂_k` neurons with `\|n̂_k/n_k − ρ\| ≤ tol`, line 16's exit condition, the difference as the scalar computes it — at ℝ, exactly. Neither loop is bounded in [1], and the first need not end: `bucketTolerance_eq_none_of_point` runs out of every `fuel` on one neuron fixed at `1` against ReLU's bucket at `0` (see Findings). So both loops take `fuel` and the result is an `Option`. [1] leaves `≈` unquantified; it is `\|n̂_k/n_k − ρ\| ≤ tol` here, `tol` a parameter. Every comparison goes through a caller's `le`, `FloatOps.le` at a machine scalar. [1] claims nothing else of Alg. 1, and soundness needs nothing of it: Prop. 4 holds at every bucket | `underspecified` — need not terminate (a neuron fixed at `1` against ReLU's bucket at `0`); no bound on either loop |
| `Def. 4` | (§4) convolutional layer, output O from input I and kernel K | n/a — a preliminary restated from the literature, not a result of this paper | `restated` |
| `Prop. 1` | interval enclosure of a zonotope (cites Althoff 2010, Prop. 2.2) | [`ZonotopeIntervalContains.lean`](../../src/CORALean/ContSet/Conversion/Real/Theorems/ZonotopeIntervalContains.lean) | `correct` |
| `Prop. 2` | (Interval Addition, cites Althoff 2010, Eq. 2.1) interval addition of a zonotope and an interval, printed as an *identity*: `Z ⊕ I = ⟨c + c_I, [G  Diag((u-l)/2)]⟩_Z` | [`PlusIntervalExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/PlusIntervalExact.lean) — the identity as printed, under the one hypothesis `I.IsNonempty`, which the paper's own `[l,u] ⊂ ℝⁿ` presupposes and `Interval.construct` does not: crossed bounds denote `∅` here while `Interval.zonotope` builds the box with them swapped. [`PlusIntervalOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/PlusIntervalOuter.lean) is the enclosure half alone, at any box | `correct` |
| `Prop. 3` | image enclosure of a nonlinear layer output set (cites Singh et al. 2018a) | n/a — restated from Singh et al. 2018, which this formalization does not draw on directly | `restated` |
| `Prop. 4` | neuron merging: constructs a sound reduced network from a merge bucket, with resulting weights/biases/interval error for layers k-1 and k+1 | [`NeuronMergingNetworkOuter.lean`](../../src/CORALean/NN/Theorems/NeuronMergingNetworkOuter.lean), [`NeuronMergingOuter.lean`](../../src/CORALean/NN/Theorems/NeuronMergingOuter.lean) | `correct` |
| `Alg. 2` | (§3.4) On-the-fly Neural Network Reduction: `H_0 ← X`, `L̂_1 ← L_1`. For `k = 2, 4, …, κ`: if `k < κ`, look ahead — `I_{k−2} ← interval(H_{k−2})` (Prop. 1), `I_k ← L_k(L̂_{k−1}(I_{k−2}))`, determine `B_{k,δ}` (Sec. 3.3), `L̂_{k−1}, L̂_k, L̂_{k+1} ← Merge` (Prop. 4); then `H_{k−1} ← enclose(L̂_{k−1}, H_{k−2})`, `H_k ← enclose(L̂_k, H_{k−1})` (Prop. 3); return `Y ← H_κ` | [`ReduceOnTheFly.lean`](../../src/CORALean/NN/Operations/ReduceOnTheFly.lean), [`ReduceOnTheFlyOuter.lean`](../../src/CORALean/NN/Theorems/ReduceOnTheFlyOuter.lean), [`ReduceOnTheFlyReducesAt.lean`](../../src/CORALean/NN/Theorems/Real/ReduceOnTheFlyReducesAt.lean), [`HoldsOfReduceOnTheFly.lean`](../../src/CORALean/NN/Theorems/HoldsOfReduceOnTheFly.lean), [`Demo/Reduce.lean`](../../src/CORALean/Examples/Demo/Reduce.lean) — `reduceOnTheFly`, one `let` per line, the loop from each `k` on being `reduceOnTheFlyFrom` and line 3's test the case split on the layers after `k + 1`; the look-ahead runs the same layers at the interval family. Written once over the scalar, and a `def` that runs: `reduceOnTheFly_outer`, at every scalar, maps every instance of the input network's image of `X` into `Y`, the reduced network's own enclosure of `X`. See the Findings. | `correct` |
| `Thm. 1` | (Sound Neural Network Reduction) Alg. 2 constructs a reduced network Φ̂_ρ satisfying the problem statement of §2.5, for any input set X and reduction rate ρ | [`Reduction.lean`](../../src/CORALean/NN/Definitions/Reduction.lean), [`API.lean`](../../src/CORALean/NN/Theorems/API.lean), [`HoldsOfReducesAt.lean`](../../src/CORALean/NN/Theorems/HoldsOfReducesAt.lean), [`HoldsOfReduceOnTheFly.lean`](../../src/CORALean/NN/Theorems/HoldsOfReduceOnTheFly.lean), [`ReduceOnTheFlyReducesAt.lean`](../../src/CORALean/NN/Theorems/Real/ReduceOnTheFlyReducesAt.lean) — `holds_of_reduceOnTheFly`: whenever Alg. 2 returns, at any `ρ`, tolerance and fuel, a specification checked on the output set `Y` it computed holds on the original network's exact image of `X`, at every scalar. At ℝ, `Real.reduceOnTheFly_reducesAt` puts what it returns in the certificate relation `ReducesAt`, and `holds_of_reducesAt` carries a specification back through any derivation of it. See the Findings. | `underspecified` — "for any reduction rate ρ" presumes `Alg. 1` ends, which it need not (see `Alg. 1`); formalized for the runs that end |
| `Cor. 1` | (Sound Compression) construction of a reduced network that compresses an uncertain image with formal error bounds, via an identity-like convolution kernel | [`SoundCompression.lean`](../../src/CORALean/Examples/EnclosesCompression.lean) — one 3-neuron instance, and the statement is purely existential: `∃ nn', construct X ⊆ construct (nn'.enclose X)` for a nonnegative `X`. The reduced network, the split it is reduced at and the error it pays live inside the proof term and not in the conclusion, which the identity network would also satisfy; the paper's ρ appears nowhere | `correct` |
| `Alg. 3` | (§4.1) Sound Compression Preprocessing: `L_{−2}, L_{−1}, L_0 ← Construct Φ_pre` (Cor. 1); `L̂_{−2}, L̂_{−1}, L̂_0 ← Reduce using I_X, ρ` (Thm. 1). `H_{−2} ← zonotope(L̂_{−2}(I_X))` (Prop. 2); `Φ'_org(·) ← Φ_org(L̂_0(L̂_{−1}(·)))`. `Y ← Execute Alg. 2 using H_{−2}, Φ'_org, ρ` (Thm. 1); return `Y` | [`CompressionPreprocessing.lean`](../../src/CORALean/NN/Operations/CompressionPreprocessing.lean), [`CompressionPreprocessingOuter.lean`](../../src/CORALean/NN/Theorems/CompressionPreprocessingOuter.lean) — `compressionPreprocessing`, written once over the scalar, and `compressionPreprocessing_outer`, at every scalar: on a nonnegative image box, Cor. 1's `X ⊂ ℝ₊`, the output set contains the image of every instance of `Φ_org`. Three readings, forced by Def. 1's alternation, which Alg. 2 relies on: `Φ_org` has at least one layer pair; the identity `L_0` is composed into `L_1` before reducing, exactly (`W_1 · I = W_1`), so line 2's `L̂_0` arrives inside `L̂_1`. And `Φ'_org` opening with the nonlinear `L̂_{−1}`, line 4 puts an identity linear layer before it, so line 5 reduces `L̂_{−1}` again, as Alg. 2 reduces every `k < κ`. See the Findings. | `correct` |
| `Cor. 2` | (Reusing Reduced Network on Subsets) a reduced network Φ̂_ρ per Thm. 1 can be reused for any subset X' ⊆ X of the original input set | [`HoldsOfReducesAtSubset.lean`](../../src/CORALean/NN/Theorems/HoldsOfReducesAtSubset.lean) | `correct` |

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`Sandwich.lean`](../../src/CORALean/NN/Definitions/Sandwich.lean)
* [`MergeRowWeight.lean`](../../src/CORALean/NN/Operations/MergeRowWeight.lean)
* [`ExistsMergeBucketAll.lean`](../../src/CORALean/NN/Theorems/ExistsMergeBucketAll.lean)
* [`ExistsMergeTolerance.lean`](../../src/CORALean/NN/Theorems/ExistsMergeTolerance.lean)
* [`MergeBucketCardMono.lean`](../../src/CORALean/NN/Theorems/MergeBucketCardMono.lean)
* [`MergeBucketMono.lean`](../../src/CORALean/NN/Theorems/MergeBucketMono.lean)
* [`MergeErrorWidthLe.lean`](../../src/CORALean/NN/Theorems/MergeErrorWidthLe.lean)
* [`MergeErrorWidthLeRow.lean`](../../src/CORALean/NN/Theorems/MergeErrorWidthLeRow.lean)

## Findings

**`Alg. 1` need not terminate, so `Thm. 1`'s "for any reduction rate ρ" holds only of the runs
that end.** Line 1 sets `δ_max ← max(u_k) − min(l_k)`, which is `0` when every neuron's bounds are
the same point; line 3 multiplies it by ten and leaves it `0`; and when no bucket holds that point,
`n̂_k = n_k`, so line 6's `n̂_k/n_k > ρ` holds at every round for every `ρ < 1` and the loop never
exits. [`BucketToleranceNone.lean`](../../src/CORALean/NN/Theorems/Real/BucketToleranceNone.lean)
proves this for one neuron fixed at `1` against ReLU's static bucket at `0` (`Eq. 5`), with the exact
order: no fuel is enough. The bisection of lines 7-16 has the same kind of gap, argued here and not
formalized: `n̂_k` moves in whole neurons, and neurons with equal bounds move together. Two neurons
both bounded by `[0.9, 1.1]` against the bucket at `0` leave line 3 at `δ_max = 2`, and at every `δ`
the bisection tries both or neither are merged, so `n̂_k/n_k` is `1` or `0`; at `ρ = 1/2` a
tolerance for `≈` narrower than `1/2` is never met. `Alg. 2` calls `Alg. 1` at every nonlinear layer
below the last, so the reduced network `Thm. 1` speaks of exists only where these loops end; here
both carry fuel, and `Alg. 2` returns `none` otherwise.

**`Alg. 3` — the unused sets of line 2.** Line 2 is Alg. 2's lines 4-7 at `Φ_pre`'s one nonlinear
layer below its last, at the box `I_X` itself. The sets its lines 10-11 would go on to compute are
unused. `zonotope(·)` is `ofInterval` into whatever representation Alg. 2 runs at.

**`Thm. 1` — the printed rate `ρ`.** “For any reduction rate ρ” is not provable as printed: Alg. 2
returns only where Alg. 1 does at every layer, and Alg. 1 need not end (Findings), so the theorem is
about every run that ends and says nothing of one that does not. The problem statement's other
clause, that constructing and verifying Φ̂ be faster than verifying Φ, is a performance claim and
not formalized.

**`Thm. 1` — the sandwich and `freeze`.** `ReducesAt.merge` consumes the sandwich
`linear / activation / linear` and resumes after it, so one derivation could not merge two
*consecutive* nonlinear layers, as Alg. 2 does at every `k < κ`. `freeze` (merge at `k`, resume
after it once for every value the bucket admits, frozen into layer `k+1`'s bias) and `widen` (a bias
known up to a box, Eq. 2) extend the relation to that, and `reducesAt_outer` covers both.

**`Alg. 2` — the result at ℝ.** `holds_of_reduceOnTheFly` is Thm. 1 for it. At ℝ,
`Real.reduceOnTheFly_reducesAt` says more: what Alg. 2 returns is a `ReducesAt` reduction of every
instance network, which names the exact layers.

**`Alg. 2` — the demo.** The demo runs it on a 2-4-2 ReLU network at `Dyadic 24`.

**`Alg. 2` — the departures.** Departures: Prop. 4 *sets* `Î'_{k+1} = W_{k+1}(·,B) I_k(B)`, which
would drop an error `I'_{k+1}` already there, and `mergeCols` *adds* it, as Eq. 4 adds per-bucket
errors — the same on an original network, and needed for Alg. 3, which runs Alg. 2 on a reduced one.
`none` where Alg. 1 runs out of fuel. And `κ = 0` returns `X`.

**`Eq. 2` — the instances of the form.** The form denotes a set of networks, one per choice of each
error's value — at one input, the printed set-valued layer's image is the union of theirs — so
`ReducibleNetwork.IsInstance` fixes each `I'_k` at one real value `c - b ∈ I'_k`, and every theorem
about Alg. 2 and Alg. 3 holds at every instance. `IsInstanceNetwork` is the same at ℝ, as the
network of layers an instance is, which is what `ReducesAt` relates.
