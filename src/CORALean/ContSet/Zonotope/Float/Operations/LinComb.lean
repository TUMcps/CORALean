import CORALean.ContSet.Interval.Float.Operations.LinComb
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.Zonotope.Float.Operations.GeneratorError
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.linComb`

The exact operation's shape, rounded: the centre is the midpoint, one generator
spans the half-difference of the centres, and the two generator blocks are
paired into half their sum and half their difference, the longer block keeping
its surplus at full width. The count stays `h₁ + h₂ + 1` as over ℝ, every
rounding going into the box.

Pairing is what costs the float layer something the loose form did not:
concatenated blocks are copied exactly, paired ones are arithmetic and round.
Halving is exact, so a single directed sum or difference is the only rounding in
a paired column, and a surplus column is a copy and does not round at all.

Two charges come out of that, and they differ in kind. The centre is stored in
place of a known bracket, which is a `residual`. Every generator's coefficient
ranges over `[-1,1]`, so its shortfall pulls both ways and is charged by
`generatorError` — one box for the whole matrix, the centre generator included,
since a row sums with no cancellation.

The generator matrix is therefore written once against a pair of directed
operations: at `addDown`/`subDown` it is what is stored, at `addUp`/`subUp` the
other end of the bracket, and the gap between them is what the box pays for.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h₁ h₂ : ℕ}

/-- The stored midpoint of the two centres. -/
def Zonotope.midpoint (a b : Vec 𝕋 n) : Vec 𝕋 n := fun i => half (addDown (a i) (b i))

/-- Storing the lower of the two directed midpoints leaves this much to pay. -/
def Zonotope.midpointResidual (a b : Vec 𝕋 n) : Interval 𝕋 n :=
  Interval.residual (fun i => half (addDown (a i) (b i)))
    (fun i => half (addUp (a i) (b i))) (Zonotope.midpoint a b)

/-- Half the sum of a generator and the column it pairs with, formed with the
given directed addition; past the shorter block the generator is copied and
nothing rounds. -/
def Zonotope.pairSum (add : 𝕋 → 𝕋 → 𝕋) (G₁ : Fin h₁ → 𝕋) (G₂ : Fin h₂ → 𝕋)
    (j : Fin h₁) : 𝕋 :=
  if hj : (j : ℕ) < h₂ then half (add (G₁ j) (G₂ ⟨j, hj⟩)) else G₁ j

/-- Half the difference, the other half of a pairing; past the shorter block it
is the second set's surplus generator, copied. -/
def Zonotope.pairDiff (sub : 𝕋 → 𝕋 → 𝕋) (G₁ : Fin h₁ → 𝕋) (G₂ : Fin h₂ → 𝕋)
    (j : Fin h₂) : 𝕋 :=
  if hj : (j : ℕ) < h₁ then half (sub (G₁ ⟨j, hj⟩) (G₂ j)) else G₂ j

/-- The whole generator matrix at one rounding: the two paired blocks and the
generator spanning the half-difference of the centres. -/
def Zonotope.linCombG (add sub : 𝕋 → 𝕋 → 𝕋) (Z₁ Z₂ : Zonotope 𝕋 n) :
    Mat 𝕋 n (Z₁.h + Z₂.h + 1) :=
  fun i => Fin.append
    (Fin.append (Zonotope.pairSum add (Z₁.G i) (Z₂.G i))
      (Zonotope.pairDiff sub (Z₁.G i) (Z₂.G i)))
    (fun _ : Fin 1 => half (sub (Z₁.c i) (Z₂.c i)))

/-- What the stored generators fall short by: the gap between the two directed
roundings, which a coefficient in `[-1,1]` then spreads either way. -/
def Zonotope.linCombGDiff (Z₁ Z₂ : Zonotope 𝕋 n) : Mat 𝕋 n (Z₁.h + Z₂.h + 1) :=
  fun i j => subUp (Zonotope.linCombG addUp subUp Z₁ Z₂ i j)
    (Zonotope.linCombG addDown subDown Z₁ Z₂ i j)

def Zonotope.linComb (Z₁ Z₂ : Zonotope 𝕋 n) : Zonotope 𝕋 n where
  h := Z₁.h + Z₂.h + 1
  c := Zonotope.midpoint Z₁.c Z₂.c
  G := Zonotope.linCombG addDown subDown Z₁ Z₂
  E := (Z₁.E.linComb Z₂.E).plus
        ((Zonotope.midpointResidual Z₁.c Z₂.c).plus
          (Zonotope.generatorError (Zonotope.linCombGDiff Z₁ Z₂)))

end CORALean.Float
