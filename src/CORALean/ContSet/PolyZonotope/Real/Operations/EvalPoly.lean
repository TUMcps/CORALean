import CORALean.ContSet.PolyZonotope.Real.Operations.Mul

/-!
# `PolyZonotope.evalPoly`

Horner's rule, coordinatewise: a degree-`n` real polynomial with given
coefficients, lowest degree first, applied to a polynomial zonotope through
repeated `mul` — `S` stays the right factor at every step, so the shared factor
count `S.p` never moves and every step's `hp` is the previous one's, carried
along rather than reproved.

Each coefficient shifts the centre directly rather than going through `plus`:
the constant carries no generators and no factors of its own, so `plus`'s
block-diagonal bookkeeping would only reintroduce, via `Fin.append`, the
identity a direct `c := … + fun _ => a` already is. `map` is unneeded too —
Horner never scales a whole accumulated set, only shifts one by a number.

`mul` sets `q := 0` and drops its independent block, so `evalPoly` inherits that
contract: the independent block takes no part, and a caller who needs those
coefficients to count runs `dependent` once, on `S`, before evaluating.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- One Horner step: `R` multiplied by `S`, then shifted by the next
coefficient. Named, `where`-built like `mul` itself, so its fields unfold
directly rather than through a record update's hidden `let`. -/
def PolyZonotope.evalPolyStep (R S : PolyZonotope (Vec ℝ n)) (hp : R.p = S.p) (a0 : ℝ) :
    PolyZonotope (Vec ℝ n) where
  p := (PolyZonotope.mul R S hp).p
  h := (PolyZonotope.mul R S hp).h
  q := (PolyZonotope.mul R S hp).q
  c := (PolyZonotope.mul R S hp).c + fun _ => a0
  G := (PolyZonotope.mul R S hp).G
  E := (PolyZonotope.mul R S hp).E
  GI := (PolyZonotope.mul R S hp).GI

/-- `evalPoly`'s recursion, paired with the proof that it never leaves `S`'s
factor count — carried along so the next step's `mul` needs no new one. -/
def PolyZonotope.evalPolyP (S : PolyZonotope (Vec ℝ n)) :
    List ℝ → {R : PolyZonotope (Vec ℝ n) // R.p = S.p}
  | [] => ⟨(⟨S.p, 0, 0, 0, Fin.elim0, fun _ => Fin.elim0, Fin.elim0⟩ : PolyZonotope (Vec ℝ n)), rfl⟩
  | a :: rest =>
      let R := PolyZonotope.evalPolyP S rest
      ⟨PolyZonotope.evalPolyStep R.1 S R.2 a, R.2⟩

/-- Horner's rule, coordinatewise, coefficients lowest degree first: `[a₀]` is
the constant `a₀`, and `a₀ :: rest` is `a₀ + S * evalPoly rest`. -/
def PolyZonotope.evalPoly (S : PolyZonotope (Vec ℝ n)) (coeffs : List ℝ) :
    PolyZonotope (Vec ℝ n) := (PolyZonotope.evalPolyP S coeffs).1

/-- The shared factor count `evalPoly` never leaves. -/
theorem PolyZonotope.evalPoly_p (S : PolyZonotope (Vec ℝ n)) (coeffs : List ℝ) :
    (S.evalPoly coeffs).p = S.p := (PolyZonotope.evalPolyP S coeffs).2

end CORALean.Real
