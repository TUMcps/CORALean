import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# Zonotopes: the linear combination of two

CORA's `@zonotope/enclose`, which is where a zonotope's `linComb` comes from:
CORA gives the representation no `linComb` of its own and `enclose` computes the
same set. The centre is the midpoint, one fresh generator spans the
half-difference of the centres — which is what lets the combination slide from
one set to the other — and the two generator blocks are paired column by column
into half their sum and half their difference, the longer block keeping its
surplus at full width.

Pairing is what makes this tighter than concatenating the blocks, at the same
count `h₁ + h₂ + 1`. Over a paired column the result reaches
`{u G₁ⱼ + v G₂ⱼ | |u| + |v| ≤ 1}`, the hull of `±G₁ⱼ` and `±G₂ⱼ`, rather than
the whole box `|u| ≤ 1, |v| ≤ 1`: the coefficients come out as
`λ β₁ⱼ ± (1-λ) β₂ⱼ`, which records that the two sides share one `λ`. Past the
shorter block there is nothing to pair with and `λ β₁ⱼ` alone still needs the
generator whole.

The columns come out in the order `sum ++ difference ++ centre` rather than
CORA's `sum ++ centre ++ difference ++ surplus`; a zonotope does not depend on
the order of its generators, and this one keeps the two blocks the same shape as
the incoming ones.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {h₁ h₂ : ℕ}

/-- Half the sum of a generator and the column it pairs with, or the generator
whole where the other block has run out. -/
noncomputable def Zonotope.pairSum (G₁ : Fin h₁ → α) (G₂ : Fin h₂ → α) (j : Fin h₁) : α :=
  if hj : (j : ℕ) < h₂ then (2:ℝ)⁻¹ • (G₁ j + G₂ ⟨j, hj⟩) else G₁ j

/-- Half the difference, the other half of a pairing; past the shorter block it
is the second set's surplus generator, whole. -/
noncomputable def Zonotope.pairDiff (G₁ : Fin h₁ → α) (G₂ : Fin h₂ → α) (j : Fin h₂) : α :=
  if hj : (j : ℕ) < h₁ then (2:ℝ)⁻¹ • (G₁ ⟨j, hj⟩ - G₂ j) else G₂ j

noncomputable def Zonotope.linComb (Z₁ Z₂ : Zonotope α) : Zonotope α where
  h := Z₁.h + Z₂.h + 1
  c := (2:ℝ)⁻¹ • (Z₁.c + Z₂.c)
  G := Fin.append (Fin.append (Zonotope.pairSum Z₁.G Z₂.G) (Zonotope.pairDiff Z₁.G Z₂.G))
        (fun _ : Fin 1 => (2:ℝ)⁻¹ • (Z₁.c - Z₂.c))

end CORALean.Real
