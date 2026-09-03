import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.Plus

/-!
# `ConPolyZono.plus`

`PolyZonotope.plus` with the two constraint systems carried along side by side,
and the reason it refines is that the carrying is pure bookkeeping: `plusA`
places the two matrices block-diagonally with `zero` in the off-blocks and `b`
concatenates, so not one entry of the constraint system is computed. Only the
centre rounds, exactly as for an unconstrained polynomial zonotope.

The interval right-hand side is where an operation that computes a bound pays for
it; `plus` computes none, and `plusB` concatenates two of them unchanged.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Two constraint systems side by side, block-diagonally: each set's rows read
only its own constraint generators. Entries are copied and the off-blocks are
`zero`, so nothing here rounds. -/
def ConPolyZono.plusA {m₁ s₁ m₂ s₂ : ℕ} (A₁ : Mat 𝕋 m₁ s₁) (A₂ : Mat 𝕋 m₂ s₂) :
    Mat 𝕋 (m₁ + m₂) (s₁ + s₂) := fun i =>
  Fin.append (fun r => Fin.append (A₁ r) (fun _ => zero))
    (fun r => Fin.append (fun _ => zero) (A₂ r)) i

/-- The two right-hand sides side by side. Copied, so nothing here rounds. -/
def ConPolyZono.plusB {m₁ m₂ : ℕ} (b₁ : Interval 𝕋 m₁) (b₂ : Interval 𝕋 m₂) :
    Interval 𝕋 (m₁ + m₂) :=
  ⟨Fin.append b₁.inf b₂.inf, Fin.append b₁.sup b₂.sup⟩

def ConPolyZono.plus (C₁ C₂ : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := C₁.p + C₂.p
  h := C₁.h + C₂.h
  q := C₁.q + C₂.q
  m := C₁.m + C₂.m
  s := C₁.s + C₂.s
  c := fun i => addDown (C₁.c i) (C₂.c i)
  G := fun i => Fin.append (C₁.G i) (C₂.G i)
  E := Real.PolyZonotope.plusE C₁.E C₂.E
  GI := fun i => Fin.append (C₁.GI i) (C₂.GI i)
  A := ConPolyZono.plusA C₁.A C₂.A
  b := ConPolyZono.plusB C₁.b C₂.b
  EC := Real.PolyZonotope.plusE C₁.EC C₂.EC
  err := (C₁.err.plus C₂.err).plus (PolyZonotope.centerResidual C₁.c C₂.c)

end CORALean.Float
