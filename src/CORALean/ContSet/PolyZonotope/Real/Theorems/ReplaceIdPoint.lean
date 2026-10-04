import CORALean.ContSet.PolyZonotope.Real.Operations.ReplaceId
import CORALean.ContSet.PolyZonotope.Real.Operations.Point

/-!
# `PolyZonotope.replaceId` evaluates the original at the renamed factors

The monomial of the renamed set at `a'` is the original monomial at `a' ∘ f`: the product of
`a'ₖ'` to the summed exponents regroups into the product over the factors, each at its new name.
So the renamed set's dependent points are the original's at the factor vectors that are constant
on the fibres of `f`; `replaceId_subset` and, for an injective `f` (a plain renaming),
`replaceId_exact` follow. Identifying two factors adds a dependency and shrinks the set.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem PolyZonotope.aux_monomial_replaceId {p p' h : ℕ} (E : Fin p → Fin h → ℕ)
    (f : Fin p → Fin p') (a' : Fin p' → ℝ) (i : Fin h) :
    PolyZonotope.monomial (fun k' i => ∑ k ∈ Finset.univ.filter (fun k => f k = k'), E k i) a' i
      = PolyZonotope.monomial E (fun k => a' (f k)) i := by -- --- PROOF ---
  unfold PolyZonotope.monomial
  -- each name's power is the product of the powers of the factors it names
  have h1 : ∀ k' : Fin p', a' k' ^ (∑ k ∈ Finset.univ.filter (fun k => f k = k'), E k i)
      = ∏ k ∈ Finset.univ.filter (fun k => f k = k'), a' (f k) ^ E k i := fun k' => by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun k hk => by rw [(Finset.mem_filter.mp hk).2]
  rw [Finset.prod_congr rfl fun k' _ => h1 k']
  exact Finset.prod_fiberwise Finset.univ f fun k => a' (f k) ^ E k i


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.replaceId_point (pZ : PolyZonotope α) {p' : ℕ} (f : Fin pZ.p → Fin p')
    (a' : Fin p' → ℝ) : (pZ.replaceId f).point a' = pZ.point (fun k => a' (f k)) := by
  unfold PolyZonotope.point
  simp only [PolyZonotope.replaceId]
  exact congrArg (fun s => pZ.c + s) (Finset.sum_congr rfl fun i _ => by
    rw [PolyZonotope.aux_monomial_replaceId])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
