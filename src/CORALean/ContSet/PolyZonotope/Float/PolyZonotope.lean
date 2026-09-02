import CORALean.ContSet.InflatedContSet.InflatedContSet
import CORALean.ContSet.PolyZonotope.Real.Instances

/-!
# Sparse polynomial zonotopes over a floating-point scalar: the representation

CORA's `polyZonotope` with its centre, dependent generators, exponent matrix and
independent generators, plus the error box that makes it an `InflatedContSet`.
The nominal part is the polynomial zonotope those stored floats describe; the
box holds what rounding has cost.

Only `c`, `G` and `GI` move to `𝕋`. The exponent matrix stays over ℕ, where
every operation on it — block-diagonal append, column addition, column
deletion — is exact, so the monomials of the nominal set are the exact layer's
monomials and not roundings of them. That is what makes the float layer's error
identical in kind to a zonotope's; `Theorems/MemGeneratorError` says what it
costs.

The error box is `err` rather than `E`, which the exponent matrix has taken.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

structure PolyZonotope (𝕋 : Type) (n : ℕ) where
  /-- The dependent factors, shared across all of `G`. -/
  p : ℕ
  /-- The dependent generators. -/
  h : ℕ
  /-- The independent generators. -/
  q : ℕ
  c : Vec 𝕋 n
  G : Mat 𝕋 n h
  E : Fin p → Fin h → ℕ
  GI : Mat 𝕋 n q
  err : Interval 𝕋 n

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (PolyZonotope 𝕋 n) (CORALean.Real.PolyZonotope (Vec ℝ n)) 𝕋 n where
  -- generators transpose: stored as a matrix here, a family of vectors there
  nominal PZ := ⟨PZ.p, PZ.h, PZ.q, toRealVec PZ.c, fun l i => toReal (PZ.G i l), PZ.E,
    fun j i => toReal (PZ.GI i j)⟩
  error PZ := PZ.err

/-! The nominal set's fields, so proofs can see through the instance. -/

theorem PolyZonotope.nominal_p [SoundFloatArithmetic 𝕋] (PZ : PolyZonotope 𝕋 n) :
    (InflatedContSet.nominal PZ).p = PZ.p := rfl

theorem PolyZonotope.nominal_h [SoundFloatArithmetic 𝕋] (PZ : PolyZonotope 𝕋 n) :
    (InflatedContSet.nominal PZ).h = PZ.h := rfl

theorem PolyZonotope.nominal_q [SoundFloatArithmetic 𝕋] (PZ : PolyZonotope 𝕋 n) :
    (InflatedContSet.nominal PZ).q = PZ.q := rfl

theorem PolyZonotope.nominal_E [SoundFloatArithmetic 𝕋] (PZ : PolyZonotope 𝕋 n) :
    (InflatedContSet.nominal PZ).E = PZ.E := rfl

/-- The nominal set spelt in this representation's own fields. Definitional, and
the reason proofs never mention `nominal`: through it every count is `PZ.h`,
where going via the instance gives the equal-but-distinct `(nominal PZ).h` that
`rw`, `ring` and `linarith` all read as a different term. -/
theorem PolyZonotope.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {PZ : PolyZonotope 𝕋 n}
    {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet PZ ↔ ∃ a : Fin PZ.p → ℝ, ∃ β : Fin PZ.q → ℝ,
      (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1) ∧ ∀ i, x i = toReal (PZ.c i)
        + (∑ l, toReal (PZ.G i l) * Real.PolyZonotope.monomial PZ.E a l)
        + ∑ j, toReal (PZ.GI i j) * β j :=
  Real.PolyZonotope.mem_construct_iff

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev PolyZonotope.construct [SoundFloatArithmetic 𝕋] (PZ : PolyZonotope 𝕋 n) :
    Set (Vec ℝ n) := InflatedContSet.construct PZ

end CORALean.Float
