# Fully Automatic Neural Network Reduction for Formal Verification

T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal
Verification". TMLR. arXiv:2305.01932.

**Source:** https://arxiv.org/html/2305.01932v3  
**Inventory:** confirmed

Reducing a network before verifying it, and the guarantee that the reduced
network's output encloses the original's — `NN.Reduction` and the merge
buckets under it.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (§2) feed-forward neural network as alternating linear/nonlinear layers, h0=x, h_k=L_k(h_{k-1}) | n/a — a preliminary restated from the literature, not a result of this paper |
| `Def. 2` | (§2) zonotope with center c and generator matrix G, Z = ⟨c,G⟩_Z [cites Girard 2005, Def. 1] | n/a — restated from Girard 2005, which this formalization does not draw on directly |
| `Def. 3` | (§2/§3) merge bucket: set of neuron indices in a nonlinear layer whose output bounds lie within tolerance δ of value y | [`MergeBucket.lean`](../../src/CORALean/NN/MergeBucket.lean) |
| `Eq. 3` | multiple disjoint merge buckets for a layer, B_{k,δ} = {B_{k,y1,δ}, B_{k,y2,δ}, ...} | n/a — the paper setting up its own notation for the buckets Eq. 4 sums errors over, not a claim to formalize |
| `Eq. 4` | overall approximation error under multiple disjoint merge buckets is the Minkowski sum of individual Prop. 4 errors, simplifying to a single weighted-interval term | [`MergeErrorSplit.lean`](../../src/CORALean/NN/Theorems/MergeErrorSplit.lean) |
| `Def. 4` | (§4) convolutional layer, output O from input I and kernel K | n/a — a preliminary restated from the literature, not a result of this paper |
| `Prop. 1` | interval enclosure of a zonotope (cites Althoff 2010, Prop. 2.2) | [`Zonotope_to_Interval.lean`](../../src/CORALean/ContSet/Conversion/Real/Zonotope_to_Interval.lean) |
| `Prop. 2` | interval addition of a zonotope and an interval (cites Althoff 2010, Eq. 2.1) | [`PlusIntervalOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/PlusIntervalOuter.lean) |
| `Prop. 3` | image enclosure of a nonlinear layer output set (cites Singh et al. 2018a) | n/a — restated from Singh et al. 2018, which this formalization does not draw on directly |
| `Prop. 4` | neuron merging: constructs a sound reduced network from a merge bucket, with resulting weights/biases/interval error for layers k-1 and k+1 | [`NeuronMergingNetworkOuter.lean`](../../src/CORALean/NN/Theorems/NeuronMergingNetworkOuter.lean), [`NeuronMergingOuter.lean`](../../src/CORALean/NN/Theorems/NeuronMergingOuter.lean) |
| `Thm. 1` | (Sound Neural Network Reduction) Alg. 2 constructs a reduced network Φ̂_ρ satisfying the problem statement of §2.5, for any input set X and reduction rate ρ | [`Reduction.lean`](../../src/CORALean/NN/Reduction.lean), [`API.lean`](../../src/CORALean/NN/Theorems/API.lean), [`HoldsOfReducesAt.lean`](../../src/CORALean/NN/Theorems/HoldsOfReducesAt.lean) |
| `Cor. 1` | (Sound Compression) construction of a reduced network that compresses an uncertain image with formal error bounds, via an identity-like convolution kernel | [`SoundCompression.lean`](../../src/CORALean/Examples/SoundCompression.lean) |
| `Cor. 2` | (Reusing Reduced Network on Subsets) a reduced network Φ̂_ρ per Thm. 1 can be reused for any subset X' ⊆ X of the original input set | [`HoldsOfReducesAtSubset.lean`](../../src/CORALean/NN/Theorems/HoldsOfReducesAtSubset.lean) |

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`ExistsMergeBucketAll.lean`](../../src/CORALean/NN/Theorems/ExistsMergeBucketAll.lean)
* [`ExistsMergeTolerance.lean`](../../src/CORALean/NN/Theorems/ExistsMergeTolerance.lean)
* [`MergeBucketCardMono.lean`](../../src/CORALean/NN/Theorems/MergeBucketCardMono.lean)
* [`MergeBucketMono.lean`](../../src/CORALean/NN/Theorems/MergeBucketMono.lean)
* [`MergeErrorWidthLe.lean`](../../src/CORALean/NN/Theorems/MergeErrorWidthLe.lean)
* [`MergeErrorWidthLeRow.lean`](../../src/CORALean/NN/Theorems/MergeErrorWidthLeRow.lean)
