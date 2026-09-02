import CORALean.ContSet.ConPolyZono.Real.Instances
import CORALean.ContSet.InflatedContSet.InflatedContSet

/-!
# Constrained polynomial zonotopes over a floating-point scalar: the representation

CORA's `conPolyZono` with its five counts, its two generator blocks and its
constraint system `A μ(α) = b`, plus the error box that makes it an
`InflatedContSet`.

`A` and `b` move to `𝕋` and are read back exactly. That is sound because the
nominal set is *defined* as what the stored floats denote — the constraint of
the nominal set is the constraint those floats state, not a rounding of some
other one. It is the operations that have to be careful, and one of them cannot
be: see below.

## Why the constraint block admits no rounding

An equality has no direction to round in. Perturb `b`, and the factor vectors
satisfying `A μ(α) = b̂` are not a superset of those satisfying `A μ(α) = b` —
they are generally a disjoint slice of the same factor cube, so neither
inclusion holds and no error box can repair it, an error box moving points and
not admissibility.

Every operation this directory carries is therefore one that touches `A` and `b`
only by copying: `plus` lays the two systems out block-diagonally, and `mtimes`
leaves them alone, the constraints living on the factors and a map of the
ambient space moving no factor. Both refine exactly as a polynomial zonotope's
do.

`and` is the one that does not, and it is the operation the representation
exists for: its agreement rows carry `b = c₂ - c₁`, a subtraction, and there is
nowhere sound to put its rounding. Making it work needs the exact layer to admit
either a slack factor with a bound on it or an interval right-hand side, the way
the float `HPolytope` has one — and both are changes to what `Real` states, so
neither is made here. `and` has no float counterpart, and that is a fact about
the specification rather than a gap in the refinement.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

structure ConPolyZono (𝕋 : Type) (n : ℕ) where
  /-- The dependent factors, shared by the generators and the constraints. -/
  p : ℕ
  /-- The dependent generators. -/
  h : ℕ
  /-- The independent generators. -/
  q : ℕ
  /-- The constraints. -/
  m : ℕ
  /-- The constraint generators. -/
  s : ℕ
  c : Vec 𝕋 n
  G : Mat 𝕋 n h
  E : Fin p → Fin h → ℕ
  GI : Mat 𝕋 n q
  A : Mat 𝕋 m s
  b : Vec 𝕋 m
  EC : Fin p → Fin s → ℕ
  err : Interval 𝕋 n

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (ConPolyZono 𝕋 n) (CORALean.Real.ConPolyZono (Vec ℝ n)) 𝕋 n where
  -- generators transpose: stored as a matrix here, a family of vectors there
  nominal C := ⟨C.p, C.h, C.q, C.m, C.s, toRealVec C.c, fun l i => toReal (C.G i l), C.E,
    fun j i => toReal (C.GI i j), toRealMat C.A, toRealVec C.b, C.EC⟩
  error C := C.err

/-- What this set's own factors must satisfy, spelt in its own fields. -/
def ConPolyZono.satisfies [SoundFloatArithmetic 𝕋] (C : ConPolyZono 𝕋 n)
    (a : Fin C.p → ℝ) : Prop :=
  Real.ConPolyZono.holds (toRealMat C.A) (toRealVec C.b) C.EC a

/-! The nominal set's fields, so proofs can see through the instance. -/

theorem ConPolyZono.nominal_A [SoundFloatArithmetic 𝕋] (C : ConPolyZono 𝕋 n) :
    (InflatedContSet.nominal C).A = toRealMat C.A := rfl

theorem ConPolyZono.nominal_b [SoundFloatArithmetic 𝕋] (C : ConPolyZono 𝕋 n) :
    (InflatedContSet.nominal C).b = toRealVec C.b := rfl

theorem ConPolyZono.nominal_EC [SoundFloatArithmetic 𝕋] (C : ConPolyZono 𝕋 n) :
    (InflatedContSet.nominal C).EC = C.EC := rfl

/-- The nominal set spelt in this representation's own fields. Definitional, and
the reason proofs never mention `nominal`: through it every count is `C.h`,
where going via the instance gives the equal-but-distinct `(nominal C).h` that
`rw`, `ring` and `linarith` all read as a different term. -/
theorem ConPolyZono.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {C : ConPolyZono 𝕋 n}
    {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet C ↔ ∃ a : Fin C.p → ℝ, ∃ β : Fin C.q → ℝ,
      (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1) ∧ C.satisfies a ∧ ∀ i, x i = toReal (C.c i)
        + (∑ l, toReal (C.G i l) * Real.PolyZonotope.monomial C.E a l)
        + ∑ j, toReal (C.GI i j) * β j :=
  Real.ConPolyZono.mem_construct_iff

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev ConPolyZono.construct [SoundFloatArithmetic 𝕋] (C : ConPolyZono 𝕋 n) :
    Set (Vec ℝ n) := InflatedContSet.construct C

end CORALean.Float
