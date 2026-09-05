import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.Mul
import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPoly

/-!
# `PolyZonotope.evalPoly`

The exact layer's Horner step, `mul` then a centre shift, rounded exactly as
`mul`/`plus` round it — except one thing neither of those owes on its own:
`R`, here, is itself only known to within its own error box, not exact, so
multiplying it by `S` also multiplies that uncertainty by however large `S` can
be. `evalPolyBoundS` bounds `|nominal S|` entrywise, and the extra box
`errorBound R.err * evalPolyBoundS S` is what a plain `mul` call would drop.

`c` rounds down, matching `plus`'s own centre; `mul`'s box and this one and the
centre's residual all add through `Interval.plus`, never combined into fewer
generators.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- A sound bound on `|nominal S|`, entrywise: the centre plus every generator's
magnitude, since every monomial is at most `1` in absolute value. -/
def PolyZonotope.evalPolyBoundS (S : PolyZonotope 𝕋 n) : Vec 𝕋 n :=
  fun i => addUp (absolute (S.c i)) (radius S.G i)

/-- One Horner step: `R` multiplied by `S` and shifted by the next coefficient,
the extra uncertainty `R` already carries priced in before `mul`'s own rounding
is added. -/
def PolyZonotope.evalPolyStep (R S : PolyZonotope 𝕋 n) (hp : R.p = S.p) (a0 : 𝕋) :
    PolyZonotope 𝕋 n where
  p := (PolyZonotope.mul R S hp).p
  h := (PolyZonotope.mul R S hp).h
  q := (PolyZonotope.mul R S hp).q
  c := fun i => addDown ((PolyZonotope.mul R S hp).c i) a0
  G := (PolyZonotope.mul R S hp).G
  E := (PolyZonotope.mul R S hp).E
  GI := (PolyZonotope.mul R S hp).GI
  err := ((PolyZonotope.mul R S hp).err.plus
      (PolyZonotope.centerResidual (PolyZonotope.mul R S hp).c (fun _ => a0))).plus
    (Interval.symmetric (fun i =>
      mulUp (PolyZonotope.errorBound R.err i) (PolyZonotope.evalPolyBoundS S i)))

/-- `evalPoly`'s recursion, paired with the proof that it never leaves `S`'s
factor count. -/
def PolyZonotope.evalPolyP (S : PolyZonotope 𝕋 n) :
    List 𝕋 → {R : PolyZonotope 𝕋 n // R.p = S.p}
  | [] => ⟨(⟨S.p, 0, 0, fun _ => zero, fun _ => Fin.elim0, fun _ => Fin.elim0, fun _ => Fin.elim0,
      ⟨fun _ => zero, fun _ => zero⟩⟩ : PolyZonotope 𝕋 n), rfl⟩
  | a :: rest =>
      let R := PolyZonotope.evalPolyP S rest
      ⟨PolyZonotope.evalPolyStep R.1 S R.2 a, R.2⟩

/-- Horner's rule, coordinatewise, coefficients lowest degree first, rounded. -/
def PolyZonotope.evalPoly (S : PolyZonotope 𝕋 n) (coeffs : List 𝕋) : PolyZonotope 𝕋 n :=
  (PolyZonotope.evalPolyP S coeffs).1

/-- The shared factor count `evalPoly` never leaves. -/
theorem PolyZonotope.evalPoly_p (S : PolyZonotope 𝕋 n) (coeffs : List 𝕋) :
    (S.evalPoly coeffs).p = S.p := (PolyZonotope.evalPolyP S coeffs).2

end CORALean.Float
