import CORALean.ContSet.Interval.Float.Interval
import CORALean.Global.Float.Instances.Dyadic.Instances

/-!
# What the demo computes in

`Dyadic 24` — binary32's significand with no exponent range, which is the one
place `Dyadic` is more generous than a machine and the reason
`SoundFloatArithmetic`'s assumption that nothing overflows is earned rather than
assumed here.

It is also the only scalar in the repository an algorithm can be *run* at:
`FloatOps` is what a definition asks for and computes, and `Dyadic`'s
`SoundFloatArithmetic` instance carries a `toReal` that computes as well, which
is what keeps every instance derived from it out of `noncomputable`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace Demo

open CORALean CORALean.Float

abbrev D := Dyadic 24

/-- `m · 2 ^ e`, so every constant below is written the way it is stored. Precision
`p` is implicit and inferred from the expected type, so the same literal serves
`Dyadic 24` and a run at a smaller precision alike. -/
def dy {p : ℕ} (m e : ℤ) : Dyadic p := ⟨m, e⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Zero width in every coordinate: what a set that has not rounded yet owes. -/
def zeroBox {p : ℕ} (n : ℕ) : Interval (Dyadic p) n := ⟨fun _ => dy 0 0, fun _ => dy 0 0⟩

end Demo


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
