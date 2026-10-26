module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
public import CORALean.ContSet.PolyZonotope.Real.Operations.Shift
public import Mathlib.Tactic.Abel
public import CORALean.NN.Graph.Operations.LinearPolyZonotope

@[expose] public section

/-!
# The graph linear layer on a polynomial zonotope is exact

An equality: the layer is an affine map of the node features, `map` is exact at its linear part
and `shift` at its bias, so nothing is given away.

## Inputs
* `W` – weight matrix
* `b` – bias vector
* `pZ` – node features as a polynomial zonotope

## Hypotheses
* none

## Conclusion
* the polynomial zonotope is exactly the image of the input set
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- `PolyZonotope.shift` is exactly the translate. -/
private theorem PolyZonotope.aux_shift_exact (pZ : PolyZonotope α) (v : α) : -- --- CONCL ---
    (fun x => x + v) '' pZ.construct = (pZ.shift v).construct := by -- --- PROOF ---
  have key : ∀ (a : Fin pZ.p → ℝ) (b : Fin pZ.q → ℝ),
      pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i + ∑ j, b j • pZ.GI j + v =
        (pZ.shift v).c + ∑ i, PolyZonotope.monomial (pZ.shift v).E a i • (pZ.shift v).G i
          + ∑ j, b j • (pZ.shift v).GI j := by
    intro a b
    show _ = pZ.c + v + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i + ∑ j, b j • pZ.GI j
    abel
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x, ⟨a, b, ha, hb, rfl⟩, rfl⟩
    exact ⟨a, b, ha, hb, key a b⟩
  · rintro y ⟨a, b, ha, hb, rfl⟩
    exact ⟨_, ⟨a, b, ha, hb, rfl⟩, key a b⟩

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.linearPolyZonotope_exact (W : Mat ℝ F₂ F₁) (b : Vec ℝ F₂)
    (pZ : PolyZonotope (Mat ℝ N F₁)) :
    GNN.linear W b '' pZ.construct = (GNN.linearPolyZonotope W b pZ).construct := by
  rw [GNN.linearPolyZonotope, ← PolyZonotope.aux_shift_exact, ← PolyZonotope.map_exact,
    ← Set.image_comp]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
