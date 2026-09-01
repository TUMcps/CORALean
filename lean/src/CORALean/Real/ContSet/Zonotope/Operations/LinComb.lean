import CORALean.Real.ContSet.Zonotope.Zonotope

/-!
# Zonotopes: the linear combination of two

CORA's `linComb`, over-approximated: the centre is the midpoint, both generator
blocks are kept, and one fresh generator spans the half-difference of the
centres, which is what lets the combination slide from one set to the other.

Sound because `λ ∈ [0,1]` scales a coefficient into `[-1,1]` again, so `λ β₁`
and `(1-λ) β₂` are coefficients of the original generator blocks and no new
ones are needed for them.

CORA takes `½(G₁+G₂)` and `½(G₁-G₂)` instead, which is tighter when the two
generator matrices correspond column by column. That needs equal generator
counts, which `h` being a field cannot promise — and padding to equal counts
turns their formula back into this one, with each generator twice over.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Zonotope.linComb (Z₁ Z₂ : Zonotope n) : Zonotope n where
  h := Z₁.h + Z₂.h + 1
  c := fun i => (Z₁.c i + Z₂.c i) / 2
  G := fun i => Fin.append (Fin.append (Z₁.G i) (Z₂.G i))
                  (fun _ : Fin 1 => (Z₁.c i - Z₂.c i) / 2)

end CORALean.Real
