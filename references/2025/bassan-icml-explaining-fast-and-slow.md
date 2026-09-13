# Explaining Fast and Slow: Abstraction and Refinement of Provable Explanations

S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining Fast and Slow:
Abstraction and Refinement of Provable Explanations". ICML 2025.

**Source:** https://arxiv.org/html/2506.08505v1  
**Inventory:** confirmed

Sufficient explanations of a network's decision, and what abstraction and
refinement do to them — `NN.suffExplanation` and its theorems.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (§2, Sufficient Explanation) subset S of input features is sufficient if fixing S (allowing others to vary within ϵ_p) never changes the argmax prediction | [`ExplainBox.lean`](../../src/CORALean/NN/Operations/ExplainBox.lean), [`SuffExplanation.lean`](../../src/CORALean/NN/Theorems/SuffExplanation.lean), [`SuffExplanationOfExact.lean`](../../src/CORALean/NN/Theorems/SuffExplanationOfExact.lean) |
| `Def. 2` | (§2, Minimal Sufficient Explanation) a sufficient explanation S with no proper subset also sufficient | [`MinSuffExplanation.lean`](../../src/CORALean/NN/Theorems/MinSuffExplanation.lean), [`MinSuffExplanationAbstract.lean`](../../src/CORALean/NN/Theorems/MinSuffExplanationAbstract.lean), [`MinSuffExplanationExact.lean`](../../src/CORALean/NN/Theorems/MinSuffExplanationExact.lean) |
| `Def. 3` | (§3, Sufficient Explanation for Abstract Network) sufficiency of S defined analogously w.r.t. an abstract network f' | [`SuffExplanationAbstract.lean`](../../src/CORALean/NN/Theorems/SuffExplanationAbstract.lean), [`SuffExplanationExact.lean`](../../src/CORALean/NN/Theorems/SuffExplanationExact.lean) |
| `Prop. 1` | (§3, Explanation Under Abstraction) for f' constructed by neuron merging, sufficiency of S w.r.t. f implies sufficiency w.r.t. f' (soundness direction across abstraction) | [`SuffExplanationTransfer.lean`](../../src/CORALean/NN/Theorems/SuffExplanationTransfer.lean) |
| `Def. 4` | (§3, Abstract Sufficient Explanation) a sufficient explanation for query ⟨f',x,S,ϵ_p⟩ is termed an abstract sufficient explanation for ⟨f,x,S,ϵ_p⟩ | [`SuffExplanationAbstract.lean`](../../src/CORALean/NN/Theorems/SuffExplanationAbstract.lean) |
| `Prop. 2` | (§4, Refined Abstract Network) relates a refined network f'' (reduction rate ρ'' > ρ', i.e. less reduced, ρ=1 being the original) built from f' to soundness of explanations | [`MinSuffExplanationAbstractOfRefined.lean`](../../src/CORALean/NN/Theorems/MinSuffExplanationAbstractOfRefined.lean), [`MinSuffExplanationExactOfRefined.lean`](../../src/CORALean/NN/Theorems/MinSuffExplanationExactOfRefined.lean) |
| `Prop. 3` | (§4, Intermediate Sufficient Explanation) suff(f',x,S,ϵ_p) ⟹ suff(f'',x,S,ϵ_p) ⟹ suff(f,x,S,ϵ_p), chaining sufficiency across abstraction levels | [`API.lean`](../../src/CORALean/NN/Theorems/API.lean), [`SuffExplanationExactOfReducesAt.lean`](../../src/CORALean/NN/Theorems/SuffExplanationExactOfReducesAt.lean), [`SuffExplanationExactOfRefined.lean`](../../src/CORALean/NN/Theorems/SuffExplanationExactOfRefined.lean), [`SuffExplanationRefined.lean`](../../src/CORALean/NN/Theorems/SuffExplanationRefined.lean) |
| `Def. 5` | (§4, Refined Sufficient Explanation) a sufficient explanation for ⟨f'',x,S,ϵ_p⟩, where f'' is a refined network built w.r.t. ⟨f,f',x,S,ϵ_p⟩ | [`SuffExplanationRefined.lean`](../../src/CORALean/NN/Theorems/SuffExplanationRefined.lean) |
| `Prop. 4` | (§4, Intermediate Minimal Sufficient Explanation) min-suff(f,x,S,ϵ_p) ⟹ min-suff(f'',x,S,ϵ_p) ⟹ min-suff(f',x,S,ϵ_p), reverse-order implication chain vs. Prop. 3 | [`MinSuffExplanationAbstractOfMin.lean`](../../src/CORALean/NN/Theorems/MinSuffExplanationAbstractOfMin.lean), [`MinSuffExplanationAbstractOfRefined.lean`](../../src/CORALean/NN/Theorems/MinSuffExplanationAbstractOfRefined.lean), [`MinSuffExplanationExactOfRefined.lean`](../../src/CORALean/NN/Theorems/MinSuffExplanationExactOfRefined.lean) |
| `Prop. 5` | (§4, Greedy Minimal Sufficient Explanation Search) Alg. 2 produces a provably sufficient and minimal explanation S for ⟨f,x,S,ϵ_p⟩, converging to the same explanation as Alg. 1 | [`MinimalAbstractExplanationSearch.lean`](../../src/CORALean/NN/MinimalAbstractExplanationSearch.lean),  |
| `Alg. 1` | (§2) Minimal Explanation Search | [`MinimalExplanationSearch.lean`](../../src/CORALean/NN/MinimalExplanationSearch.lean), [`SuffExplanationMono.lean`](../../src/CORALean/NN/Theorems/SuffExplanationMono.lean) |
| `Alg. 2` | (§4) Minimal Abstract Explanation Search: abstraction-refinement loop producing a minimal sufficient explanation; line 9 is part of its refinement/verification step | [`MinimalAbstractExplanationSearch.lean`](../../src/CORALean/NN/MinimalAbstractExplanationSearch.lean), [`MinSuffExplanationAbstract.lean`](../../src/CORALean/NN/Theorems/MinSuffExplanationAbstract.lean), [`MinSuffExplanationCounterexample.lean`](../../src/CORALean/NN/Theorems/MinSuffExplanationCounterexample.lean), [`SuffExplanationOfEnclose.lean`](../../src/CORALean/NN/Theorems/SuffExplanationOfEnclose.lean), [`SuffExplanationOfNeuronMerging.lean`](../../src/CORALean/NN/Theorems/SuffExplanationOfNeuronMerging.lean), [`SuffExplanationRefined.lean`](../../src/CORALean/NN/Theorems/SuffExplanationRefined.lean), [`SuffExplanationTransfer.lean`](../../src/CORALean/NN/Theorems/SuffExplanationTransfer.lean) |
| `Def. 6` | (App. A, Neural Network) formal definition: y=f(x), h_k layer recursion with L_k(h_{k-1}):=σ(W_k h_{k-1}+b_k) | n/a — a preliminary restated from the literature, not a result of this paper |
| `Def. 7` | (App. A, Abstract Neural Network) analogous definition for an abstract network f' with set-valued output | [`Enclose.lean`](../../src/CORALean/NN/Operations/Enclose.lean) |
| `Lemma 1` | (App. A, Neuron-Merging Construction, cites Ladner & Althoff 2023, Prop. 4) construction of a sound abstract/reduced network by merging a set of neurons B_k in layer k | n/a — restated; tracked as `Thm. 1` on [Fully Automatic Neural Network Reduction](../2023/ladner-tmlr-network-reduction.md) |
| `Sec. 4` | The abstraction-and-refinement scheme, and the running example that shows the transfer of a sufficient explanation runs one way only. | [`SuffExplanationConverseFails.lean`](../../src/CORALean/NN/Theorems/SuffExplanationConverseFails.lean) |

## Findings

**`Alg. 2` — `ℱ` decides nothing.** `ℱ` is initialized to `[n]` at l. 1, read in the loop
header at l. 2, and written once, at l. 13, where it drops the very feature the header has
already handed to the body; l. 21 returns `𝒮`. No write of `ℱ` can therefore change which
features are visited or what comes back, and the proof in §A.6 never mentions it. The
formalization drops it. [`MinimalAbstractExplanationSearch.lean`](../../src/CORALean/NN/MinimalAbstractExplanationSearch.lean)

**`Prop. 5` — minimality is argued at the wrong candidate set.** §A.6 assumes the returned
`𝒮` is not minimal, takes an `i` with `𝒮∖{i}` still sufficient, and concludes that "we cannot
have found a counterexample in [l.] 10". But the query answered while `i` was being processed
was about `𝒮ᵢ∖{i}` for the running `𝒮ᵢ ⊇ 𝒮`, not about `𝒮∖{i}`. The step needs sufficiency to
be monotone in the pinned set, which the paper states nowhere and which holds only because
`Def. 1`'s radius is nonnegative. [`SuffExplanationMono.lean`](../../src/CORALean/NN/Theorems/SuffExplanationMono.lean)

**`Prop. 5` — both claims need the refinement to reach `f`, and nothing says it does.** §A.6
disposes of the do-while with "eventually after all refinement steps on the original network".
Line 19 is `while true` and l. 7 and l. 13 are its only exits, so on a schedule that stops
short of `f` the loop does not return at all — let alone the smaller explanation §4 promises
under a timeout. `Prop. 2` gives only a strictly finer `f''`, never that the sequence reaches
`f` in finitely many steps; the schedule that does is an implementation choice in §B.2.
`hlast` is that hypothesis written down. [`MinimalAbstractExplanationSearch.lean`](../../src/CORALean/NN/MinimalAbstractExplanationSearch.lean)
