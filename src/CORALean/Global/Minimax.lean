module

public import Mathlib.Analysis.Normed.Order.Lattice

@[expose] public section

/-!
# A minimax inequality over two compact sets

[1, Lemma 3.1]. The paper's shared codomain "compact interval `I ⊂ Rⁿ`" would make `f`, `g`
vector-valued, with no order for `min`/`max`; [1, Thm. 3.2] applies the lemma at `f = ‖x_B - x‖₂`, a
scalar, so `I ⊂ Rⁿ` is a misprint for `I ⊂ R`. `I` is dropped: boundedness comes from continuity on
a compact domain, and nothing uses the linear structure of `Rⁿ`, so `C1`, `C2` sit in a bare
topological space. The inequality is one line once `x* ∈ C1` attaining `max_{x∈C1} min_{y∈C2}
f(x,y)` exists, which needs `x ↦ min_{y∈C2} f(x,y)` continuous, a fragment of Berge's maximum
theorem (`IsCompact.continuous_sInf`, reached from continuity on `C1 ×ˢ C2` alone by
`aux_continuousOn_sInf_image`). `C1` carries `Nonempty` for its `sSup` to be attained, `C2` not.

## Inputs
* none

## Hypotheses
* `hC1` – the first set is compact
* `hC1ne` – the first set is nonempty
* `hC2` – the second set is compact
* `hf` – the function is continuous on the product
* `hg` – the bound function is continuous on the first set
* `hle` – the inner minimum is bounded pointwise by the bound function

## Conclusion
* the maximum of the inner minima is at most the maximum of the bound function

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for Reachability
      Analysis of Nonlinear Systems". Proceedings of the 24th International Conference on Hybrid
      Systems: Computation and Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type*} [TopologicalSpace α] {C1 C2 : Set α} {f : α → α → ℝ} {g : α → ℝ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Berge's parametrized-infimum fragment: `x ↦ min_{y∈C2} f(x,y)` is continuous
from joint continuity of `f` on `C1 ×ˢ C2` and compactness of `C2` alone —
`C1` needs neither compactness nor nonemptiness here. -/
theorem aux_continuousOn_sInf_image (hC2 : IsCompact C2)
    (hf : ContinuousOn (Function.uncurry f) (C1 ×ˢ C2)) : -- --- CONCL ---
    ContinuousOn (fun x => sInf (f x '' C2)) C1 := by -- --- PROOF ---
  rw [continuousOn_iff_continuous_restrict]
  -- both variables restricted to subtypes, where the joint function is continuous everywhere
  have hcont : Continuous (Function.uncurry fun x : C1 => fun y : C2 => f x.1 y.1) := by
    have hmap : Continuous fun p : C1 × C2 => ((p.1 : α), (p.2 : α)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    have hmem : ∀ p : C1 × C2, ((p.1 : α), (p.2 : α)) ∈ C1 ×ˢ C2 := fun p => ⟨p.1.2, p.2.2⟩
    exact hf.comp_continuous hmap hmem
  haveI : CompactSpace C2 := isCompact_iff_compactSpace.mp hC2
  have hcts := IsCompact.continuous_sInf
    (f := fun x : C1 => fun y : C2 => f x.1 y.1) (K := (Set.univ : Set C2)) isCompact_univ hcont
  simp only [Set.image_univ] at hcts
  -- `range (f x)` over the subtype is `f x '' C2` over `α`
  refine hcts.congr fun x => ?_
  rw [Set.restrict_apply, Set.range_comp' (f x.1) (Subtype.val : C2 → α), Subtype.range_val]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 3.1]: over compact `C1`, `C2` with `C1` nonempty, a pointwise bound
of `min_{y∈C2} f(x,y)` by `g(x)` on `C1` lifts to a bound of the same shape
between the two quantities' maxima on `C1`. -/
theorem minimax_le (hC1 : IsCompact C1) (hC1ne : C1.Nonempty) (hC2 : IsCompact C2)
    (hf : ContinuousOn (Function.uncurry f) (C1 ×ˢ C2)) (hg : ContinuousOn g C1)
    (hle : ∀ x ∈ C1, sInf (f x '' C2) ≤ g x) : -- --- CONCL ---
    sSup ((fun x => sInf (f x '' C2)) '' C1) ≤ sSup (g '' C1) := by -- --- PROOF ---
  -- the point of `C1` where `min_{y∈C2} f(x,y)` attains its own maximum
  obtain ⟨x, hx, hxeq⟩ :=
    hC1.exists_sSup_image_eq hC1ne (aux_continuousOn_sInf_image hC2 hf)
  rw [hxeq]
  exact (hle x hx).trans (le_csSup (hC1.bddAbove_image hg) (Set.mem_image_of_mem g hx))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
