import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# Zonotopes: the linear combination of two

CORA's `linComb`, over-approximated: the centre is the midpoint, both generator
blocks are kept, and one fresh generator spans the half-difference of the
centres, which is what lets the combination slide from one set to the other.

Sound because `λ ∈ [0,1]` scales a coefficient into `[-1,1]` again, so `λ β₁`
and `(1-λ) β₂` are coefficients of the original generator blocks and no new
ones are needed for them.

CORA has no `linComb` for zonotopes; its `enclose` computes this set as
`⟨½(c₁+c₂), [½(G₁+G₂), ½(c₁-c₂), ½(G₁-G₂), G_excess]⟩`, pairing generators
column by column and keeping the larger set's surplus at full width. That has
the same count `h₁ + h₂ + 1` and is tighter, since it records that `λ β₁` and
`(1-λ) β₂` share one `λ`; keeping the two blocks whole is the looser choice
this file makes.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

noncomputable def Zonotope.linComb (Z₁ Z₂ : Zonotope α) : Zonotope α where
  h := Z₁.h + Z₂.h + 1
  c := (2:ℝ)⁻¹ • (Z₁.c + Z₂.c)
  G := Fin.append (Fin.append Z₁.G Z₂.G)
        (fun _ : Fin 1 => (2:ℝ)⁻¹ • (Z₁.c - Z₂.c))

end CORALean.Real
