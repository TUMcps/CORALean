import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

/-!
# A box as a polynomial zonotope, over a floating-point scalar

The box goes into the error box, and the nominal part is the origin. Exact, and
the only encoding here that is: a centre with one generator per coordinate has to
round the centre and then reach both ends from wherever it landed, as
`Interval.zonotope` does, while `err` already *is* an interval and holds this one
unchanged.

Nothing downstream can tell the two apart. `err` and an independent generator
block are equally excluded from `mul` and `evalPoly`, and `dependent` frees both
into fresh factors, so the choice costs no precision at any later step.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def Interval.polyZonotope (I : Interval (Vec 𝕋 n)) : PolyZonotope 𝕋 n where
  p := 0
  h := 0
  q := 0
  c := fun _ => zero
  G := Fin.elim0
  E := fun _ => Fin.elim0
  GI := Fin.elim0
  err := I


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.polyZonotope_contains (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ I.polyZonotope.construct := fun x hx => by
  -- the nominal part is the origin, so the box carries the whole point
  refine ⟨0, PolyZonotope.mem_nominalSet_iff.mpr
    ⟨Fin.elim0, Fin.elim0, fun k => k.elim0, fun j => j.elim0, fun i => ?_⟩, x, hx, zero_add x⟩
  show (0 : ℝ) = toReal (zero : 𝕋) + (∑ l : Fin 0, _) + ∑ j : Fin 0, _
  rw [toReal_zero]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
