import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# The monomial of a renamed factor list

The monomial of the exponent matrix whose row `k'` adds the rows of the factors sent to `k'` by `f`,
at `a'`, is the original monomial at `a' ∘ f`: the powers regroup along the fibres of `f`.
`replaceId` and `subs` (a shared identifier) are stated through it.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Adding the exponent rows of the factors a map identifies composes the factor vector. -/
theorem PolyZonotope.monomial_replaceId {p p' h : ℕ} (E : Fin p → Fin h → ℕ)
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
