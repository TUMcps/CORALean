import CORALean.Float.ContSet.Zonotope.Zonotope

/-!
# `Zonotope.linComb`

Both generator blocks are kept exactly, so only the two centre-derived vectors
round: the midpoint that becomes the new centre, and the half-difference that
becomes the sliding generator. Each pays into the error box, leaving the count
at `h₁ + h₂ + 1` as over ℝ.

Halving is exact, so a directed sum or difference is the only rounding in
either. The two are charged differently: the midpoint is stored in place of a
known bracket, which is a `residual`, while the sliding generator carries a
coefficient ranging over `[-1,1]`, so its shortfall pulls both ways and needs a
symmetric box.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The stored midpoint of the two centres. -/
def Zonotope.midpoint (a b : Vec 𝕋 n) : Vec 𝕋 n := fun i => half (addDown (a i) (b i))

/-- The stored half-difference of the two centres: the generator that lets the
combination slide from one set to the other. -/
def Zonotope.halfDiff (a b : Vec 𝕋 n) : Vec 𝕋 n := fun i => half (subDown (a i) (b i))

/-- Storing the lower of the two directed midpoints leaves this much to pay. -/
def Zonotope.midpointResidual (a b : Vec 𝕋 n) : Interval 𝕋 n :=
  Interval.residual (fun i => half (addDown (a i) (b i)))
    (fun i => half (addUp (a i) (b i))) (Zonotope.midpoint a b)

/-- What the sliding generator falls short by, over the whole range of its
coefficient: the stored value rounds down, so the gap to the upper rounding
bounds it, and `[-1,1]` spreads that gap symmetrically. -/
def Zonotope.halfDiffError (a b : Vec 𝕋 n) : Interval 𝕋 n :=
  Interval.symmetric fun i =>
    subUp (half (subUp (a i) (b i))) (half (subDown (a i) (b i)))

def Zonotope.linComb (Z₁ Z₂ : Zonotope 𝕋 n) : Zonotope 𝕋 n where
  h := Z₁.h + Z₂.h + 1
  c := Zonotope.midpoint Z₁.c Z₂.c
  G := fun i => Fin.append (Fin.append (Z₁.G i) (Z₂.G i))
                  (fun _ : Fin 1 => Zonotope.halfDiff Z₁.c Z₂.c i)
  E := (Z₁.E.linComb Z₂.E).plus
        ((Zonotope.midpointResidual Z₁.c Z₂.c).plus (Zonotope.halfDiffError Z₁.c Z₂.c))

end CORALean.Float
