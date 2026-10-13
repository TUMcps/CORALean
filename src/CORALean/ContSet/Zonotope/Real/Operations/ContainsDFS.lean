import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.CoeffNorm
import Mathlib.Algebra.BigOperators.Intervals

/-!
# `Zonotope.containsDFS`

`[1, Alg. 1]`, the depth-first vertex enumeration, CORA's `contains_(Z, S, 'exact:venum')`
(`priv_zonotopeContainment_vertexEnumeration`): is the zonotope `Ẑ` inside the ellipsotope
`E = d + H(B)`? The generators are sorted by their `E`-norm, descending (line 1). A node is a
sign choice `σ` for the first `k` of them, valued by `er_k(σ) = ‖c - d + ∑_{i<k} gᵢ σᵢ‖_E`
(the paper's Eq. 8) and pruned by `h_k(σ) = er_k(σ) + ∑_{i ≥ k} ‖gᵢ‖_E`
(`[1, Eq. 9]`). The stack is a list with its top at the head, so `push σ₋; push σ₊`
is `σ₊ :: σ₋ :: rest`. The `while` loop runs on `fuel`, `2^{m+1}` (one more than the nodes
of the search tree), so it is total; with that fuel the exhausted branch is never taken.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[1, Alg. 1]`: `true` iff `Z ⊆ d + H(B)`, for a surjective `H`. -/
noncomputable def Zonotope.containsDFS (Z : Zonotope (Vec ℝ n)) (H : E →ₗ[ℝ] Vec ℝ n)
    (d : Vec ℝ n) : Bool :=
  let nrm := coeffNorm H
  -- line 1: the generators sorted by their norm, descending
  let ord := (List.finRange Z.h).mergeSort fun i j => if nrm (Z.G j) ≤ nrm (Z.G i) then true
    else false
  let g : ℕ → Vec ℝ n := fun i => (ord.map Z.G).getD i 0
  let er : List Bool → ℝ := fun σ =>
    nrm (Z.c - d + ∑ i ∈ Finset.range σ.length, (if σ.getD i false then (1 : ℝ) else -1) • g i)
  let h : List Bool → ℝ := fun σ => er σ + ∑ i ∈ Finset.Ico σ.length Z.h, nrm (g i)
  -- lines 2-6
  let M := nrm (Z.c - d)
  if M > 1 then false else Zonotope.containsDFS.loop er h (2 ^ (Z.h + 1)) [[]]
where
  /-- Lines 7-25: pop, prune, push both children, stop at a value above `1`. -/
  loop (er h : List Bool → ℝ) : ℕ → List (List Bool) → Bool
    | 0, _ => false
    | _ + 1, [] => true
    | f + 1, σ :: rest =>
      if h σ ≤ 1 then loop er h f rest
      else
        let σp := σ ++ [true]
        let σm := σ ++ [false]
        let stack := if er σp ≥ er σm then σp :: σm :: rest else σm :: σp :: rest
        if max (er σm) (er σp) > 1 then false else loop er h f stack

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
