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
| `Eq. 1` | graph Laplacian regularization loss L = L0 + λ L_reg used in prior semi-supervised graph learning | — |
| `Eq. 2` | layer-wise propagation rule: H^(l+1) = σ( D̃^(-1/2) Ã D̃^(-1/2) H^(l) W^(l) ), with Ã = A + I_N, D̃_ii = Σ_j Ã_ij | [`Conv.lean`](../src/CORALean/NN/Graph/Conv.lean) |
| `Eq. 3` | spectral graph convolution as g_θ ⋆ x = U g_θ U^T x via graph Fourier transform | — |
| `Eq. 4` | Chebyshev polynomial truncated expansion approximating g_θ'(Λ) up to order K | — |
| `Eq. 5` | K-localized spectral filter g_θ' ⋆ x ≈ Σ_{k=0}^K θ'_k T_k(L̃) x | — |
