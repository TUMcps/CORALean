module

public import CORALean.ContSet.SetIntersection.Theorems.Basic

@[expose] public section

/-!
# A bijective image of an intersection, member by member, is exact

`F (⋂ᵢ Sᵢ) = ⋂ᵢ F Sᵢ` for a bijective `F`, so a family whose members are the exact images
`Tᵢ = F Sᵢ` denotes exactly the image of the intersection. Injectivity alone gives `⊆` the other
way for a nonempty family only; surjectivity covers the empty one, `F univ = univ`. Stated at
`Fin`-indexed families, as a fixed-arity bundle (`ZonoBundle`) lists its members; at a linear
map of a zonotope bundle it is the exact case of [1, Prop. 1], `L` of full rank read as
invertible.

## Inputs
* `k` – number of members
* `f` – members of the operand
* `g` – members of the result
* `F` – map

## Hypotheses
* `hF` – `F` bijective
* `h` – each `g i` is the image of `f i` under `F`

## Conclusion
* the result is the image of the operand's intersection

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S T α β : Type} [ContSet S α] [ContSet T β]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Members that are the exact images under a bijection denote the image of the intersection. -/
theorem SetIntersection.memberwise_image_exact {k : ℕ} {f : Fin k → S} {g : Fin k → T}
    (F : α → β) (hF : Function.Bijective F)
    (h : ∀ i, ContSet.construct (g i) = F '' ContSet.construct (f i)) : -- --- CONCL ---
    ContSet.construct (⟨List.ofFn g⟩ : SetIntersection T)
      = F '' ContSet.construct (⟨List.ofFn f⟩ : SetIntersection S) := by -- --- PROOF ---
  rw [SetIntersection.construct_ofFn, SetIntersection.construct_ofFn, Set.image_iInter hF]
  exact Set.iInter_congr h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
