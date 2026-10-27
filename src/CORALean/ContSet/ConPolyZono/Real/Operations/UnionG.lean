module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.unionG`

The generators of [1, Thm. 1]: half the difference of the two centers, whose
factor is the branch selector, and then both operands' generators unchanged. The
center of the union is half their sum, so `α₁ = 1` reaches `c₁` and `α₁ = -1`
reaches `c₂`.

## Inputs
* `h₁` – generators of first
* `h₂` – generators of second
* `α` – ambient type
* `c₁` – first center
* `c₂` – second center
* `G₁` – first generators
* `G₂` – second generators

## Output
* generators of the union

## References

* [1] [N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.](../../../../../../references/2023/kochdumper-constrained-polyzonotopes.md)
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Half the center difference, then both operands' generators. -/
noncomputable def ConPolyZono.unionG {h₁ h₂ : ℕ} {α : Type} [AddCommGroup α] [Module ℝ α]
    (c₁ c₂ : α) (G₁ : Fin h₁ → α) (G₂ : Fin h₂ → α) : Fin (1 + (h₁ + h₂)) → α :=
  Fin.append (fun _ => (2 : ℝ)⁻¹ • (c₁ - c₂)) (Fin.append G₁ G₂)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
