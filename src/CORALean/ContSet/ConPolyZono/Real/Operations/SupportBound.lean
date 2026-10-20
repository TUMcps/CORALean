module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import CORALean.Global.SupportFunction.SupportFunction

@[expose] public section

/-!
# `ConPolyZono.supportBound`

CORA's `@conPolyZono/supportFunc_` [1], which bounds the support function by branch and bound over
the dependent factors under the constraints. The bound `u` on the dependent part (the points
`c + Σ αᴱ G` over the factors in the unit box that satisfy the constraints) is an argument,
standing for that search, exactly as in `PolyZonotope.supportBound`; the independent block adds
its own extent `Σ |c(GIⱼ)|`. The result is an upper bound, equal to CORA's value only when `u`
is tight, which is not claimed. CORA's `'lower'` and `'range'` types, the tolerance and
the point attaining the value are not modelled.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `c` – direction as a linear functional
* `u` – bound on the dependent part

## Output
* bound on the set in that direction

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The dependent part's bound `u` over the feasible factors, plus the independent block's own
extent in the direction `c`. -/
noncomputable def ConPolyZono.supportBound (cPZ : ConPolyZono α) (c : α →ₗ[ℝ] ℝ)
    (u : SupportBound (cPZ.polyZonotope.point '' cPZ.cons.construct) c) :
    SupportBound cPZ.construct c where
  val := u.val + ∑ j, |c (cPZ.GI j)|
  le := by
    rintro _ ⟨a, β, hβ, hs, rfl⟩
    have hdep : c (cPZ.polyZonotope.point a) ≤ u.val := u.le _ ⟨a, hs, rfl⟩
    have hind : c (∑ j, β j • cPZ.GI j) ≤ ∑ j, |c (cPZ.GI j)| := by
      rw [map_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [map_smul, smul_eq_mul]
      calc β j * c (cPZ.GI j) ≤ |β j * c (cPZ.GI j)| := le_abs_self _
        _ = |β j| * |c (cPZ.GI j)| := abs_mul _ _
        _ ≤ 1 * |c (cPZ.GI j)| := mul_le_mul_of_nonneg_right (hβ j) (abs_nonneg _)
        _ = |c (cPZ.GI j)| := one_mul _
    have hx : c (cPZ.polyZonotope.point a + ∑ j, β j • cPZ.GI j) ≤ u.val + ∑ j, |c (cPZ.GI j)| := by
      rw [map_add]
      exact add_le_add hdep hind
    exact hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
