module

public import CORALean.ContSet.SetIntersection.Theorems.Basic

@[expose] public section

/-!
# A memberwise enclosure of an intersection is outer

`Φ (⋂ᵢ Sᵢ) ⊆ ⋂ⱼ Tⱼ` once every result member `Tⱼ` holds `Φ` of some operand member `Sᵢ`, for
any monotone set operation `Φ`: an image, a set-valued image (`⋃ A ∈ M, A ''`), or the identity
when members are dropped. Stated at families indexed by `Fin`, as a fixed-arity bundle
(`ZonoBundle`) lists its members, so a bundle's operation that maps or drops members is outer by
this theorem with each member's own guarantee, and needs no theorem of its own. At a linear
map of a zonotope bundle it is the enclosure `L Z_∩ ⊆ {L Z₁, …, L Z_s}_∩` of [1, Prop. 1].

## Inputs
* `k` – number of operand members
* `l` – number of result members
* `f` – operand members
* `g` – result members
* `Φ` – set operation

## Hypotheses
* `hΦ` – `Φ` monotone
* `h` – each `g j` encloses `Φ` of some `f i`

## Conclusion
* `Φ` of the operand's intersection lies in the result

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

variable {S T α β : Type} [ContSet S α] [ContSet T β]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Each result member enclosing `Φ` of an operand member encloses `Φ` of the intersection. -/
theorem SetIntersection.memberwise_outer {k l : ℕ} {f : Fin k → S} {g : Fin l → T}
    (Φ : Set α → Set β) (hΦ : Monotone Φ)
    (h : ∀ j, ∃ i, Φ (ContSet.construct (f i)) ⊆ ContSet.construct (g j)) : -- --- CONCL ---
    Φ (ContSet.construct (⟨List.ofFn f⟩ : SetIntersection S))
      ⊆ ContSet.construct (⟨List.ofFn g⟩ : SetIntersection T) := by -- --- PROOF ---
  rw [SetIntersection.construct_ofFn, SetIntersection.construct_ofFn]
  refine Set.subset_iInter fun j => ?_
  obtain ⟨i, hi⟩ := h j
  exact (hΦ (Set.iInter_subset _ i)).trans hi

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
