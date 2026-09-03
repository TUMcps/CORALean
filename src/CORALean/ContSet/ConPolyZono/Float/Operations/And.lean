import CORALean.ContSet.ConPolyZono.Float.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
import CORALean.ContSet.ConPolyZono.Real.Operations.And

/-!
# `ConPolyZono.and`

The operation the representation exists for, and the one an equality right-hand
side kept out of this layer. Only one quantity is computed — the agreement rows'
right-hand interval — and it is computed outward, which is what the exact
layer's tolerance is for.

Here a set is a nominal one plus an error box, so the two points that have to
agree are `y₁ + e₁` and `y₂ + e₂`, and it is the *nominal* points the rows can
speak about. Those differ by `e₂ - e₁`, which the two boxes bound, so the rows
say the nominal points agree only to within

  `c₂ − c₁ + [err₂.inf − err₁.sup, err₂.sup − err₁.inf]`,

each end rounded away from the other. The rounding of `c₂ − c₁` therefore costs
nothing extra: it goes into an interval that had to be widened anyway.

The result keeps `C₁`'s error box and only `C₁`'s generator block, both for the
same reason — the point it denotes is `y₁ + e₁`, and `C₂` enters through the
constraint system alone. `C₂`'s generator columns are kept at `zero` so that the
agreement rows have somewhere to read the second point.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The row pinning the two points together in coordinate `i`. Entries are
copied and `neg` is exact, so nothing here rounds. -/
def ConPolyZono.agreeRow (C₁ C₂ : ConPolyZono 𝕋 n) (i : Fin n) :
    Fin (C₁.h + C₂.h) → 𝕋 :=
  Fin.append (fun l => C₁.G i l) fun l => neg (C₂.G i l)

/-- The constraint matrix of `andDep`: the two systems block-diagonally over the
constraint columns and blind to the generator columns, then the agreement rows,
blind to the constraint columns. -/
def ConPolyZono.andA (C₁ C₂ : ConPolyZono 𝕋 n) :
    Mat 𝕋 (C₁.m + C₂.m + n) (C₁.s + C₂.s + (C₁.h + C₂.h)) := fun i =>
  Fin.append
    (fun r => Fin.append (ConPolyZono.plusA C₁.A C₂.A r) (fun _ => zero))
    (fun r => Fin.append (fun _ => zero) (ConPolyZono.agreeRow C₁ C₂ r)) i

/-- The agreement rows' right-hand interval, and the only thing `and` computes:
the difference of the two centres, widened by how far the two error boxes let
the nominal points stand apart, each end rounded outward. -/
def ConPolyZono.andAgree (C₁ C₂ : ConPolyZono 𝕋 n) : Interval 𝕋 n :=
  ⟨fun i => addDown (subDown (C₂.c i) (C₁.c i)) (subDown (C₂.err.inf i) (C₁.err.sup i)),
   fun i => addUp (subUp (C₂.c i) (C₁.c i)) (subUp (C₂.err.sup i) (C₁.err.inf i))⟩

/-- The two systems' own bounds, then the agreement rows'. -/
def ConPolyZono.andB (C₁ C₂ : ConPolyZono 𝕋 n) : Interval 𝕋 (C₁.m + C₂.m + n) :=
  ⟨Fin.append (ConPolyZono.plusB C₁.b C₂.b).inf (ConPolyZono.andAgree C₁ C₂).inf,
   Fin.append (ConPolyZono.plusB C₁.b C₂.b).sup (ConPolyZono.andAgree C₁ C₂).sup⟩

/-- Sound where both independent blocks are empty; `and` arranges that. -/
def ConPolyZono.andDep (C₁ C₂ : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := C₁.p + C₂.p
  h := C₁.h + C₂.h
  q := 0
  m := C₁.m + C₂.m + n
  s := C₁.s + C₂.s + (C₁.h + C₂.h)
  c := C₁.c
  G := fun i => Fin.append (C₁.G i) fun _ => zero
  E := Real.PolyZonotope.plusE C₁.E C₂.E
  GI := fun _ => Fin.elim0
  A := ConPolyZono.andA C₁ C₂
  b := ConPolyZono.andB C₁ C₂
  EC := Real.ConPolyZono.appendE (Real.PolyZonotope.plusE C₁.EC C₂.EC)
          (Real.PolyZonotope.plusE C₁.E C₂.E)
  err := C₁.err

def ConPolyZono.and (C₁ C₂ : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n :=
  ConPolyZono.andDep C₁.dependent C₂.dependent

end CORALean.Float
