import CORALean.ContSet.InflatedContSet.API
import CORALean.ContSet.Zonotope.Real.API

/-!
# Zonotopes over a floating-point scalar: the representation

CORA's `zonotope` with its centre and generator matrix, plus the error box that
makes it an `InflatedContSet`. The nominal part is the zonotope those stored
floats describe; the box holds what rounding has cost.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   18-August-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

structure Zonotope (𝕋 : Type) (n : ℕ) where
  h : ℕ
  c : Vec 𝕋 n
  G : Mat 𝕋 n h
  E : Interval 𝕋 n

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (Zonotope 𝕋 n) (CORALean.Real.Zonotope (Vec ℝ n)) 𝕋 n where
  -- generators transpose: stored as a matrix here, a family of vectors there
  nominal Z := ⟨Z.h, toRealVec Z.c, fun j i => toReal (Z.G i j)⟩
  error Z := Z.E

/-! The nominal zonotope's fields, so proofs can see through the instance. -/

theorem Zonotope.nominal_h [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) :
    (InflatedContSet.nominal Z).h = Z.h := rfl

theorem Zonotope.nominal_c [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) :
    (InflatedContSet.nominal Z).c = toRealVec Z.c := rfl

theorem Zonotope.nominal_G [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) :
    (InflatedContSet.nominal Z).G = fun j i => toReal (Z.G i j) := rfl

/-- The nominal set spelt in this zonotope's own fields. Definitional, and the
reason proofs never mention `nominal`: through it every count is `Z.h`, where
going via the instance gives the equal-but-distinct `(nominal Z).h` that `rw`,
`ring` and `linarith` all read as a different term. -/
theorem Zonotope.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {Z : Zonotope 𝕋 n}
    {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet Z ↔ ∃ β : Vec ℝ Z.h, (∀ j, |β j| ≤ 1) ∧
      ∀ i, x i = toReal (Z.c i) + ∑ j, toReal (Z.G i j) * β j :=
  Real.Zonotope.mem_construct_iff

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev Zonotope.construct [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) : Set (Vec ℝ n) :=
  InflatedContSet.construct Z

end CORALean.Float
