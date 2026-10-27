module

public import CORALean.ContSet.SetIntersection.Theorems.Basic

@[expose] public section

/-!
# A pairwise enclosure of two intersections is outer

`Φ (⋂ᵢ Sᵢ) (⋂ⱼ S'ⱼ) ⊆ ⋂ₚ Tₚ` once every result member `Tₚ` holds `Φ` of some pair of operand
members, for any set operation `Φ` monotone in both arguments: a Minkowski sum, `Set.linComb`.
The two-argument form of `memberwise_outer`, stated at `Fin`-indexed families as a bundle
(`ZonoBundle`) lists its members, so a bundle's operation over every pair of members is outer by
this theorem with each pair's own guarantee: at the Minkowski sum of zonotope bundles, the
enclosure of [1, Prop. 2], of which a bundle plus one zonotope is the one-member case.

## Inputs
* `k` – number of first members
* `k'` – number of second members
* `l` – number of result members
* `f` – first members
* `f'` – second members
* `g` – result members
* `Φ` – binary set operation

## Hypotheses
* `hΦ` – `Φ` monotone in both arguments
* `h` – each `g p` encloses `Φ` of some pair

## Conclusion
* `Φ` of the two intersections lies in the result

## References

* [1] [M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.](../../../../../references/2011/althoff-cdc-zonotope-bundles.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S S' T α α' β : Type} [ContSet S α] [ContSet S' α'] [ContSet T β]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Each result member enclosing `Φ` of a pair of operand members encloses `Φ` of the two
intersections. -/
theorem SetIntersection.pairwise_outer {k k' l : ℕ} {f : Fin k → S} {f' : Fin k' → S'}
    {g : Fin l → T} (Φ : Set α → Set α' → Set β)
    (hΦ : ∀ ⦃A B : Set α⦄ ⦃A' B' : Set α'⦄, A ⊆ B → A' ⊆ B' → Φ A A' ⊆ Φ B B')
    (h : ∀ p, ∃ i i', Φ (ContSet.construct (f i)) (ContSet.construct (f' i'))
      ⊆ ContSet.construct (g p)) : -- --- CONCL ---
    Φ (ContSet.construct (⟨List.ofFn f⟩ : SetIntersection S))
        (ContSet.construct (⟨List.ofFn f'⟩ : SetIntersection S'))
      ⊆ ContSet.construct (⟨List.ofFn g⟩ : SetIntersection T) := by -- --- PROOF ---
  rw [SetIntersection.construct_ofFn, SetIntersection.construct_ofFn,
    SetIntersection.construct_ofFn]
  refine Set.subset_iInter fun p => ?_
  obtain ⟨i, i', hp⟩ := h p
  exact (hΦ (Set.iInter_subset _ i) (Set.iInter_subset _ i')).trans hp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
