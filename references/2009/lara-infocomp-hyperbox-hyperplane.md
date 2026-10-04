# On the Hyperbox – Hyperplane Intersection Problem

C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.

**Source:** https://repositorio.ufla.br/bitstreams/51400f6d-500c-4466-89aa-06b95bc35200/download (the journal's PDF from the Universidade Federal de Lavras repository, 7 pages, read in full; text extracted with `pypdf`, so over-bars, e.g. `v̄ᵢ` in Lemma 6.2, are read from the proofs that use them). The journal's own page, infocomp.dcc.ufla.br article 278, now answers 404.  
**Inventory:** confirmed (the numbered items are Equations (1)-(5), Definitions 1-5, Lemmas 6.1, 6.2, 6.4, 6.5, Corollary 6.3 with three cases, Algorithms 1-3 and Figures 1-5; the claims of Sec. 1, Sec. 6.2 and Sec. 6.3 are rows of their own, named by section)

The algorithm behind CORA's `boxPlaneIntersect`, which `@conZonotope/priv_potVertices` calls for
the vertices of a constrained zonotope with one constraint and at least five generators (fewer,
`boxPlaneIntersectNaive`, Alg. 1). The vertices of a box cut by a hyperplane lie on its edges;
Alg. 2 finds them by exploring only the border region of the box's vertex graph, from vertices
below the plane whose upward edges cross it. CORALean formalizes the characterization of the
vertices (exactly the points of the cut with at most one coordinate strictly inside), both
algorithms as returning exactly that set, every lemma and corollary of Sec. 6, the iteration bound
behind `O(nm)`, and the two mappings of Sec. 6.3. Alg. 2 is written as a recursion over the
s-faces it would push, which visits the same faces depth first.

CORA's implementation was checked against the paper by transcribing it to Python and comparing
with an edge enumeration on 1500 random inputs of the shape `priv_potVertices` passes: no
difference. It does not sort the box, which the paper's Alg. 2 needs, but it partitions the root
face once and expands every piece to all its vertices (`partZ`, `aux_fillStack`), so it visits
every vertex and is in effect the naive method, complete at exponential cost; no finding.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. 1` | The vertices of the intersection polygon of a box `B` and a plane `P` lie on the edges of `B`, perhaps at vertices; a naive algorithm takes each edge and finds its intersection with the plane. | [`MemExtremePointsInterHyperplaneIff.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/MemExtremePointsInterHyperplaneIff.lean) — exactly: the extreme points of `B ∩ {Σᵢ aᵢxᵢ = α}`, every `aᵢ ≠ 0`, are its points with at most one coordinate strictly inside | `correct` |
| `Sec. 2` | Related work on hypercube graphs and box-plane intersection in 3D. | n/a — related work | `not-a-claim` |
| `Eq. 1` | `B = [a₁, b₁] × … × [aₙ, bₙ]`; the vertices `V(B)`, their labels `L(v)`, and adjacency by one differing label, an edge `[u, v]`. | n/a — definitions; CORALean's `Interval` and `Interval.corner` at a label vector | `not-a-claim` |
| `Sec. 3 (edges)` | A hyperbox has `n2^{n-1}` edges [5, 2], so the naive algorithm is exponential. | n/a — restated from [5] and [2] | `restated` |
| `Eq. 2` | The hyperplane `Σᵢ xᵢ = α`. | [`BoxPlane.lean`](../../src/CORALean/ContSet/Interval/Real/Definitions/BoxPlane.lean) — `Interval.hyperplane 1 α`, and the scaled `Σᵢ aᵢxᵢ = α` of Sec. 6.3 | `correct` |
| `Def. 1` | A box is located at the origin if every `aᵢ = 0`, `B = [0, b₁] × … × [0, bₙ]`. | n/a — a definition; the box `⟨0, b⟩` | `not-a-claim` |
| `Def. 2` | An ordered box is one at the origin with `b₁ ≤ b₂ ≤ … ≤ bₙ`. | n/a — a definition; `Monotone b` | `not-a-claim` |
| `Def. 3` | A squashed face `s ∈ {0, 1, *}ⁿ` represents the vertices `V(s)` obtained by filling its undefined labels; for `s = (b₁, …, b_j, *, …, *)`, `\|V(s)\| = 2^{n-j}`. | [`BoxPlane.lean`](../../src/CORALean/ContSet/Interval/Real/Definitions/BoxPlane.lean), [`CardPrefixFace.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/CardPrefixFace.lean) — the s-faces with a defined prefix, the only ones the algorithm forms | `correct` |
| `Def. 4` | `v` is a (low) border vertex if `∃k, v_k = 0 ∧ Σᵢ vᵢ ≤ α < b_k + Σᵢ vᵢ`. | n/a — a definition; the vertices `Interval.mem_exploreBNVisits` reaches | `not-a-claim` |
| `Def. 5` | `w` is a high border vertex if `∃k, w_k = b_k ∧ Σᵢ wᵢ ≥ α > Σᵢ wᵢ - b_k`; using low or high border vertices is equivalent. | n/a — a definition; the equivalence is `Lemma 6.4` | `not-a-claim` |
| `Sec. 4` | The problem: `B ∩ P` is a hyperpolygon of `n - 1` dimensions, represented by its vertices `C`, which lie on the edges of `B`; an algorithm finds them in `O(nm)`, `m` the number of vertices. | n/a — the problem statement; its claims are the rows `Sec. 1` and `Sec. 6.2`. The cut can also be empty, a point or of lower dimension, which the vertex representation covers | `not-a-claim` |
| `Eq. 3` | The edge `e_uv(t) = v + t(u - v)`, `t ∈ [0, 1]`. | n/a — the parametrization `Eq. 4` uses | `not-a-claim` |
| `Eq. 4` | The edge meets the plane at `t⋆ = (α - Σᵢ vᵢ)/Σᵢ(uᵢ - vᵢ)`; if `t⋆ ∈ [0, 1]` the edge and the hyperplane intersect. | [`EdgeMemHyperplaneIff.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/EdgeMemHyperplaneIff.lean) — `e_uv(t)` is on the plane iff `t = t⋆`, for a nonzero denominator, the edge's length | `correct` |
| `Alg. 1` | `Naive(B, α)`: for every edge, if `0 ≤ t⋆ ≤ 1` add `e_uv(t⋆)` to `L`; `L` is the list of solutions, the vertices of the intersection. | [`BoxPlaneIntersectNaive.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/BoxPlaneIntersectNaive.lean), [`BoxPlaneIntersectNaiveEq.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/BoxPlaneIntersectNaiveEq.lean) — the output is exactly the set of extreme points of `B ∩ P`, for a box with positive side lengths and `n ≥ 1` | `correct` |
| `Lemma 6.1` | For an ordered box and `s = (v₁, …, v_j, *, …, *)`, `j < n`, with `Σ_{i≤j} vᵢ ≤ α < b_{j+1} + Σ_{i≤j} vᵢ` (Eq. 5), exactly one `v ∈ V(s)` has `Σᵢ vᵢ ≤ α`: `s` has a unique border vertex. | [`ExistsUniqueBorderVertex.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExistsUniqueBorderVertex.lean) | `correct` |
| `Lemma 6.2` | For `s = (v₁, …, v_j, *, …)`, `s' = (v₁, …, v_k, *, …)`, `j < k`, `V(s') ⊂ V(s)`: `V(s')` and `V((v₁, …, v_{i-1}, v̄ᵢ, *, …))`, `i = j+1, …, k`, partition `V(s)`. | [`PrefixFacePartition.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/PrefixFacePartition.lean) — union and pairwise disjointness, for `k ≤ n` | `correct` |
| `Cor. 6.3 (1)` | `j = n`: a vertex `v` is a solution iff `Σⱼ vⱼ = α`; otherwise at least one solution is at its edges iff `Σⱼ vⱼ < α` and `∃vᵢ = 0` with `bᵢ > α - Σⱼ vⱼ`, namely `(v₁, …, α - Σⱼ vⱼ, …, vₙ)`. | [`VertexEdgeSolutionIff.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/VertexEdgeSolutionIff.lean), [`VertexEdgeSolutionCounterexample.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/VertexEdgeSolutionCounterexample.lean) — the "iff" for the edges `v` raises, open at the far end, and the named point a solution; for every edge at `v` the "only if" fails, with a counterexample | `underspecified` — "at its edges" holds for the upward edges of a low vertex, see the findings |
| `Cor. 6.3 (2)` | `j < n` and Eq. 5: if `α = Σ_{i≤j} vᵢ` the border vertex is the unique solution, otherwise the solutions are found by exploring the edges adjacent to the border vertex of `s`. | [`ExtremePointsFaceEq5.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExtremePointsFaceEq5.lean) — the vertices of the face cut by the plane are exactly the border vertex with one free coordinate raised to `α - Σ_{i≤j} vᵢ`, and the border vertex alone when that is `0` | `correct` |
| `Cor. 6.3 (3)` | `j < n`, Eq. 5 failing: solutions exist if `Σ_{i≤j} vᵢ < α` and `Σ_{i≤j} vᵢ + Σ_{i>j} bᵢ ≥ α`, found by partitioning with Lemma 6.2. | [`FaceInterHyperplaneNonempty.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/FaceInterHyperplaneNonempty.lean) — the face meets the plane, with or without Eq. 5 | `correct` |
| `Alg. 2` | `EXPLORE BN(B, α, s)`: pop an s-face, set `w` to its labels followed by the largest prefix of upper bounds `b_{j+1}, …, b_k` keeping `Σ ≤ α` (line 6), add `FIND SOLUTIONS(w)`, and if `k < n` push the pieces of `P(v, v')` but `v'`; for an ordered box at the origin it determines all vertices of the intersection. | [`ExploreBNVisits.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/ExploreBNVisits.lean), [`ExploreBN.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/ExploreBN.lean), [`ExploreBNStepSpec.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExploreBNStepSpec.lean), [`ExploreBNVisitsSumLe.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExploreBNVisitsSumLe.lean), [`MemExploreBNVisits.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/MemExploreBNVisits.lean), [`ExploreBNEqExtremePoints.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExploreBNEqExtremePoints.lean), [`ExploreBNNegCounterexample.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExploreBNNegCounterexample.lean) — the output is exactly the set of extreme points of `B ∩ P`, for `b` ordered and positive and `α ≥ 0`; for `α < 0` line 6 has no `k` and, taking `k = j`, the output holds a point outside the box | `underspecified` — needs `α ≥ 0`, see the findings |
| `Alg. 3` | `FIND SOLUTIONS(v, B, α)`: with `α' = α - Σᵢ vᵢ`, `{v}` if `α' = 0`, else `v` with `vᵢ ← α'` for every `i` with `bᵢ > α'` and `vᵢ = 0`: the solutions adjacent to or at `v`. | [`FindSolutions.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/FindSolutions.lean), [`ExploreBNEqExtremePoints.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExploreBNEqExtremePoints.lean) — for a vertex below the plane, its outputs are vertices of the cut, and every vertex of the cut on an upward edge of `v` is one | `correct` |
| `Sec. 6.1` | Starting from high border vertices can find more solutions per vertex (Fig. 3); as a rule of thumb solve the direct problem when `k ≤ n - k`, else the complementary one. | n/a — a heuristic for efficiency; the equivalence it rests on is `Lemma 6.4` | `not-a-claim` |
| `Lemma 6.4` | If `c` solves the intersection of `B` with `Σᵢ xᵢ = α`, its complement `c'ᵢ = bᵢ - cᵢ` solves it with `α' = Σᵢ bᵢ - α`. | [`MemExtremePointsComplementIff.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/MemExtremePointsComplementIff.lean) — for the vertices of the two cuts, both ways | `correct` |
| `Lemma 6.5` | For `s'` with a single border node and `k < n`, each element of `P(s, s')` has at least one solution. | [`PieceHasBorderVertex.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/PieceHasBorderVertex.lean), [`PieceSolutionCounterexample.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/PieceSolutionCounterexample.lean) — every piece holds a vertex below the plane whose raised edge meets it; a piece's own face can miss the plane, with a counterexample | `underspecified` — "has a solution" holds as a solution adjacent to its vertices, see the findings |
| `Sec. 6.2` | Every face pushed in line 12 produces a solution, the loop runs at most `m` times, each step costs `O(n)`, so the algorithm is `O(nm)`. | [`ExploreBNVisitsLengthLeCard.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExploreBNVisitsLengthLeCard.lean) — the number of iterations is at most the number of solutions, for `0 ≤ α ≤ Σᵢ bᵢ`; the `O(n)` per step is a running cost, which a definition does not state | `underspecified` — needs the plane to meet the box, see the findings |
| `Sec. 6.3 (scaling)` | `[0, b₁] × … × [0, bₙ]` with `Σᵢ βᵢxᵢ = α`, `βᵢ ≠ 0`, maps to `B⋆ = [0, β₁b₁] × … × [0, βₙbₙ]` with `Σᵢ xᵢ = α`, every solution `c⋆` to `(c⋆₁/β₁, …, c⋆ₙ/βₙ)`. | [`MemExtremePointsScaleIff.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/MemExtremePointsScaleIff.lean), [`ScaleBoxCounterexample.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ScaleBoxCounterexample.lean) — with `[min(0, βᵢbᵢ), max(0, βᵢbᵢ)]`, the vertices correspond exactly; read literally, `[0, βᵢbᵢ]` is empty for `βᵢ < 0`, with a counterexample | `underspecified` — for a negative `βᵢ` the interval's bounds are crossed, see the findings |
| `Sec. 6.3 (translation)` | `[a₁, b₁] × … × [aₙ, bₙ]` with `Σᵢ xᵢ = α` maps to `[0, b₁ - a₁] × …` with `Σᵢ x⋆ᵢ = α - Σᵢ aᵢ`, every solution `c⋆` to `c⋆ + a`. | [`MemExtremePointsTranslateIff.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/MemExtremePointsTranslateIff.lean) — the vertices correspond exactly | `correct` |
| `Sec. 6.3 (general problem)` | These pre- and post-processing mappings allow solving the intersection of any hyperbox with any hyperplane without changing the overall time complexity. | [`ExploreBNUnorderedCounterexample.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExploreBNUnorderedCounterexample.lean), [`ExploreBNSort.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExploreBNSort.lean) — Alg. 2 misses a vertex of an unordered box, which neither mapping orders; sorting the coordinates first and permuting back gives exactly the vertices | `underspecified` — a coordinate sort is also needed, see the findings |
| `Sec. 7` | Experiments: random boxes of dimension 20, varying `α` and the dimension; the proposed algorithm is linear in the number of solutions, the naive one constant. | n/a — experiments | `not-a-claim` |
| `Fig. 1` | A cube cut by a plane, the six vertices `c₁, …, c₆` on its edges. | n/a — an illustration of `Sec. 1` | `not-a-claim` |
| `Fig. 2` | One s-face `(b₁, *, *)` represents four vertices. | n/a — an illustration of `Def. 3` | `not-a-claim` |
| `Fig. 3` | Two solutions reached from two low border vertices or from one high one. | n/a — an illustration of `Sec. 6.1` | `not-a-claim` |
| `Fig. 4` | Running time of the naive algorithm and `EXPLORE BN` against the number of solutions, `n = 20`. | n/a — experiments | `not-a-claim` |
| `Fig. 5` | Running time of `EXPLORE BN` for `n = 20, 22, 24`, without and with the improvement of Sec. 6.1. | n/a — experiments | `not-a-claim` |
| `Sec. 8` | The algorithm is `O(mn)`, considerably faster than the naive one; a further improvement lowers the complexity. | n/a — conclusions; the bound is `Sec. 6.2` | `not-a-claim` |

## Findings

**`Alg. 2` needs `α ≥ 0`.** Line 6 asks for the maximum `k ≤ n` with
`Σ_{i≤j} vᵢ + Σ_{i=j+1}^k bᵢ ≤ α`, which does not exist at the root `(*, …, *)` when `α < 0`; the
proof of `Lemma 6.4` remarks that a solution needs `0 ≤ α ≤ Σᵢ bᵢ`, the algorithm does not check
it. Reading line 6 as `k = j` when nothing qualifies, `FIND SOLUTIONS(0)` with `α' = α < 0`
lowers a coordinate to `α`: on `[0, 1]` with `α = -1` the output is `{-1}`, outside the box,
while the cut is empty
([`ExploreBNNegCounterexample.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExploreBNNegCounterexample.lean)).
CORA's `aux_exploreBN` skips a `w` above the plane, which avoids it.

**`Sec. 6.3`'s mappings do not order the box.** Alg. 2 assumes an ordered box, `b₁ ≤ … ≤ bₙ`:
`Lemma 6.1` uses it to rule out every vertex of `V(s')` but one. Scaling and translation put the
box at the origin and the plane in the form `Σᵢ xᵢ = α`, but leave the order of the `bᵢ` as it
was, and the text claims the two "allow us to solve the general problem". On `[0, 2] × [0, 1]`
with `Σᵢ xᵢ = 3/2`, line 6 stops at `k = 0` (`b₁ = 2 > 3/2`), nothing is pushed, and the output
`{(3/2, 0)}` misses the vertex `(1/2, 1)`
([`ExploreBNUnorderedCounterexample.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExploreBNUnorderedCounterexample.lean)).
Sorting the coordinates first, `O(n log n)` once, and permuting the solutions back gives exactly
the vertices ([`ExploreBNSort.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExploreBNSort.lean)).
CORA's `boxPlaneIntersect` does not sort either, and is nonetheless complete, as it expands the
root's partition to all vertices.

**`Sec. 6.3 (scaling)` crosses the bounds for a negative coefficient.** The text allows every
`βᵢ ≠ 0` and maps the box to `[0, βᵢbᵢ]`; for `βᵢ < 0` that interval is written with its bounds
crossed. On `[0, 1]`, `-x = -1/2` has the vertex `1/2`, while `[0, -1]` read as an interval holds
no point
([`ScaleBoxCounterexample.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ScaleBoxCounterexample.lean)).
Read as the interval between its bounds, `[min(0, βᵢbᵢ), max(0, βᵢbᵢ)]` — and translated to the
origin afterwards, as CORA's `aux_boxScaling` and `aux_boxTranslation` do — the vertices
correspond exactly.

**`Cor. 6.3 (1)`'s "iff" is about the edges the vertex raises.** Read for every edge at `v`, the
"only if" fails: on `[0, 1]` with `α = 1/2`, the vertex `1` has `Σⱼ vⱼ = 1 > α`, yet its edge down
to `0` holds the solution `1/2`
([`VertexEdgeSolutionCounterexample.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/VertexEdgeSolutionCounterexample.lean)).
For the edges `v` raises, open at the far end — the convention of the low border vertices,
`Def. 4` — it holds as printed. With `bᵢ = α - Σⱼ vⱼ` the solution is the far vertex itself, which
the strict `>` leaves to that vertex.

**`Lemma 6.5`'s solutions are adjacent to the piece, not in it.** On `[0, 1]²` with
`Σᵢ xᵢ = 3/2`, line 6 gives `k = 1` at the root and the piece `(0, *)`, whose face `{0} × [0, 1]`
never reaches the plane
([`PieceSolutionCounterexample.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/PieceSolutionCounterexample.lean)).
What holds, and what `Sec. 6.2` uses, is the reading of Alg. 2's output specification — solutions
"adjacent to or at the vertices `V(s)`": every piece holds a vertex below the plane with an
upward edge meeting it, here `(0, 1)` and its edge to `(1, 1)` through `(1/2, 1)`. The paper's
proof also invokes the order of the box, which the statement does not need.

**`Sec. 6.2` needs the plane to meet the box.** "Each iterative step finds one or more solutions"
fails for `α > Σᵢ bᵢ`: the root raises every coordinate, `FIND SOLUTIONS` finds nothing, and the
loop runs once for `m = 0`. For `0 ≤ α ≤ Σᵢ bᵢ` every visited vertex has a solution, distinct
vertices have distinct solutions (a solution determines the vertex below it), and the visits are
distinct, so there are at most `m`.
