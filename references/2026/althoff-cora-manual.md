# CORA Manual (v2026)

```bibtex
@manual{althoff2026cora,
  author = {Althoff, M. and Kochdumper, N. and Ladner, T. and Perschl, M. and Wetzlinger, M.},
  title = {CORA Manual (v2026)},
  publisher = {Technische Universität München},
  year = {2026}
}
```

**Source:** https://tumcps.github.io/CORA/data/archive/manual/Cora2026Manual.pdf (218 pages, text extracted with `pymupdf`; the sections below were read, the rest of the manual was searched for the class names only)  
**Inventory:** partial (only the sections that define a construction a CORALean file takes: the set classes capsule, emptySet and fullspace, the support function, the output equation of a linear system, the discrete-time nonlinear system, the grid partition, the Markov chain and the safe and unsafe set specifications; the manual's other sections, its operation tables and its examples are not rows)

The CORA manual states, class by class, what CORA's set and system classes denote. It is cited
for those definitions only. It does not mention the classes `syntaxTree`, `finiteSignal`,
`finiteKleeneSignalBuilder`, `tentativeKleeneSignal`, `reachSetAnalyzer` or `trajectoryAnalyzer`,
which therefore have no row here.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. 2.1.4.9` | (supportFunc) The support function of a set S ⊂ ℝⁿ in a direction l ∈ ℝⁿ is the maximum of lᵀx over x ∈ S; the lower bound is the minimum. | [`SupportFunction.lean`](../../src/CORALean/ContSet/SupportFunction/Real/SupportFunction.lean) — a set held as its support function over all directions, `h(ℓ) = sup {ℓ x}` | `correct` |
| `Sec. 2.2.1.7` | (Capsules) A capsule is the Minkowski sum of a line segment L = {c + gα : α ∈ [-1, 1]} and a sphere S = {x : ‖x‖₂ ≤ r}, with center c, generator g and radius r ≥ 0, Eq. (10). | [`Capsule.lean`](../../src/CORALean/ContSet/Capsule/Real/Capsule.lean), [`Capsule.lean`](../../src/CORALean/ContSet/Capsule/Float/Capsule.lean) | `correct` |
| `Sec. 2.2.2.1` | (Empty set) The empty set O = ∅ ⊂ ℝⁿ, built from its dimension n. | [`EmptySet.lean`](../../src/CORALean/ContSet/EmptySet/Real/EmptySet.lean) | `correct` |
| `Sec. 2.2.2.2` | (Fullspace) The fullspace FS = ℝⁿ, built from its dimension n. | [`Fullspace.lean`](../../src/CORALean/ContSet/Fullspace/Real/Fullspace.lean) | `correct` |
| `Sec. 4.2.1` | (Linear systems, output) The output of a linear system is y(t) = Cx(t) + Du(t) + k + v(t), Eq. (33); the row is the part Cx + Du + k, without the sensor noise v. | [`OutputEq.lean`](../../src/CORALean/ContDynamics/OutputEq/OutputEq.lean) | `correct` |
| `Sec. 4.2.8` | (Nonlinear discrete-time systems) x[i+1] = f(x[i], u[i]) and y[i] = g(x[i], u[i]) with sampling time Δt, Eqs. (43) and (44). | [`NonlinearSysDT.lean`](../../src/CORALean/ContDynamics/NonlinearSysDT/NonlinearSysDT.lean) | `correct` |
| `Sec. 5.1` | (State space partitioning) The state space is cut into axis-aligned cells, the class `partition`. | [`GridPartition.lean`](../../src/CORALean/DiscrDynamics/GridPartition/GridPartition.lean) | `correct` |
| `Sec. 5.2` | (Markov chains) The transition matrix of a Markov chain is Φ_ij = P(z(k+1) = i \| z(k) = j), so that p̂(k+1) = Φ p̂(k); the row is the transition matrix, not the initial probability p̂₀. | [`MarkovChain.lean`](../../src/CORALean/DiscrDynamics/MarkovChain/MarkovChain.lean) | `correct` |
| `Sec. 7.3` | (Class specification) A specification of type 'unsafeSet' holds when R(t) ∩ S = ∅ and one of type 'safeSet' when R(t) ⊆ S, for all t ∈ [t₀, t_f]; the row is these two types, not 'invariant', 'logic' or 'custom'. | [`Specification.lean`](../../src/CORALean/Specification/Specification.lean) | `correct` |
