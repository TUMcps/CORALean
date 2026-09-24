# Semi-Supervised Classification with Graph Convolutional Networks

T. N. Kipf and M. Welling. "Semi-Supervised Classification with Graph Convolutional
Networks". ICLR, 2017.

**Source:** https://arxiv.org/html/1609.02907v4  
**Inventory:** confirmed

Cited for one thing: the layerwise propagation rule that `GCNLayer`
implements. The verification results about it are in the GCN paper, not here.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Eq. 1` | graph Laplacian regularization loss L = L0 + λ L_reg used in prior semi-supervised graph learning | n/a — background the paper states on the way to Eq. 2 |
| `Eq. 2` | layer-wise propagation rule: H^(l+1) = σ( D̃^(-1/2) Ã D̃^(-1/2) H^(l) W^(l) ), with Ã = A + I_N, D̃_ii = Σ_j Ã_ij | [`MessagePassing.lean`](../../src/CORALean/NN/Graph/Operations/MessagePassing.lean) — the propagation `H ↦ P H W` with `P = D̃^(-1/2) Ã D̃^(-1/2)`, **without** the activation σ, which is a separate layer here as it is in the GCN paper's `Def. 4`. `GNN.degree` reads column sums where `D̃_ii = Σ_j Ã_ij` is a row sum; the two agree for the symmetric `Ã` the file's docstring assumes |
| `Eq. 3` | spectral graph convolution as g_θ ⋆ x = U g_θ U^T x via graph Fourier transform | n/a — spectral graph convolution, background for Eq. 2 |
| `Eq. 4` | Chebyshev polynomial truncated expansion approximating g_θ'(Λ) up to order K | n/a — the Chebyshev truncation, background for Eq. 2 |
| `Eq. 5` | K-localized spectral filter g_θ' ⋆ x ≈ Σ_{k=0}^K θ'_k T_k(L̃) x | n/a — the localized filter, background for Eq. 2 |
