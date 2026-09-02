import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
import CORALean.ContSet.PolyZonotope.Real.Operations.Plus

/-!
# `ConPolyZono.dependent`

`PolyZonotope.dependent` with the constraints carried along: every independent
generator made dependent, by giving it a fresh factor that appears in it alone
and to the first power. Exact, and cheaply so — a factor occurring in one
generator only is as free as the coefficient it replaces.

Here it earns more than it does for a polynomial zonotope. The constraints reach
the dependent factors and nothing else, so an operation stated as a constraint —
`and` above all — is exact only on a set whose coefficients are all dependent.
`dependent` is what makes that a restriction on nothing: it is applied first,
and it loses nothing.

The fresh factors take exponent zero in every constraint row, which is what
`padE` says. They have to: the constraints were written against the original
factors, and a fresh factor appearing in one would silently change them.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConPolyZono.dependent (C : ConPolyZono α) : ConPolyZono α where
  p := C.p + C.q
  h := C.h + C.q
  q := 0
  m := C.m
  s := C.s
  c := C.c
  G := Fin.append C.G C.GI
  E := PolyZonotope.plusE C.E (PolyZonotope.identE C.q)
  GI := Fin.elim0
  A := C.A
  b := C.b
  EC := ConPolyZono.padE C.EC C.q

/-- Fresh factors at exponent zero constrain nothing, so the system says of the
widened factor vector exactly what it said of the original. -/
theorem ConPolyZono.holds_padE_iff {p m s : ℕ} (A : Mat ℝ m s) (b : Vec ℝ m)
    (EC : Fin p → Fin s → ℕ) (r : ℕ) (a : Fin (p + r) → ℝ) :
    ConPolyZono.holds A b (ConPolyZono.padE EC r) a
      ↔ ConPolyZono.holds A b EC (fun k => a (Fin.castAdd r k)) := by
  have hm : PolyZonotope.monomial (ConPolyZono.padE EC r) a
      = PolyZonotope.monomial EC (fun k => a (Fin.castAdd r k)) :=
    funext fun l => ConPolyZono.monomial_padE EC r a l
  simp only [ConPolyZono.holds, hm]

omit [AddCommGroup α] [Module ℝ α] in
theorem ConPolyZono.satisfies_dependent_iff (C : ConPolyZono α)
    (a : Fin (C.p + C.q) → ℝ) :
    C.dependent.satisfies a ↔ C.satisfies (fun k => a (Fin.castAdd C.q k)) :=
  ConPolyZono.holds_padE_iff C.A C.b C.EC C.q a

end CORALean.Real
