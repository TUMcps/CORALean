module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombOuter
public import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombValueDependent

@[expose] public section

/-!
# `linComb` is exactly [1, Def. 7] where neither set has independent generators

The result is [1, Prop. 14], whose construction is `PolyZonotope.linComb`: the paper's
`0.5[G₁ G₁ G₂ -G₂]` at the exponent matrix `linCombE` assembles. `⊆` is `linComb_outer`, which
needs no hypothesis. `⊇` is `linComb_value_dependent` (every factor vector of `linComb` names a
segment point) and is what the independent generators would break, hence `q = 0` on both
sides. The fresh factor is the segment parameter under `λ = (1+α)/2`, and `|α| ≤ 1` is exactly
`λ ∈ [0,1]`. It is the convex hull only where both operands are convex.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `h₁` – first has no independent generators
* `h₂` – second has no independent generators

## Conclusion
* the linear combination set is exactly the result

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.linComb_exact_of_dependent (pZ₁ pZ₂ : PolyZonotope α)
    (h₁ : pZ₁.q = 0) (h₂ : pZ₂.q = 0) : -- --- CONCL ---
    Set.linComb pZ₁.construct pZ₂.construct = (pZ₁.linComb pZ₂).construct := by -- --- PROOF ---
  refine Set.eq_of_subset_of_subset (PolyZonotope.linComb_outer pZ₁ pZ₂) ?_
  rintro x ⟨a, β, ha, hβ, rfl⟩
  -- the fresh factor, whose unit bound is the segment parameter's `λ ∈ [0,1]`
  obtain ⟨hl₀, hl₁⟩ := abs_le.mp (ha (Fin.natAdd (pZ₁.p + pZ₂.p) (0 : Fin 1)))
  exact ⟨pZ₁.c + ∑ i, PolyZonotope.monomial pZ₁.E
        (fun k => a (Fin.castAdd 1 (Fin.castAdd pZ₂.p k))) i • pZ₁.G i
      + ∑ j, (0 : ℝ) • pZ₁.GI j,
    ⟨fun k => a (Fin.castAdd 1 (Fin.castAdd pZ₂.p k)), fun _ => 0,
      fun k => ha _, fun _ => by simp, rfl⟩,
    pZ₂.c + ∑ i, PolyZonotope.monomial pZ₂.E
        (fun k => a (Fin.castAdd 1 (Fin.natAdd pZ₁.p k))) i • pZ₂.G i
      + ∑ j, (0 : ℝ) • pZ₂.GI j,
    ⟨fun k => a (Fin.castAdd 1 (Fin.natAdd pZ₁.p k)), fun _ => 0,
      fun k => ha _, fun _ => by simp, rfl⟩,
    (1 + a (Fin.natAdd (pZ₁.p + pZ₂.p) (0 : Fin 1))) / 2, ⟨by linarith, by linarith⟩,
    PolyZonotope.linComb_value_dependent pZ₁ pZ₂ h₁ h₂ a β⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
