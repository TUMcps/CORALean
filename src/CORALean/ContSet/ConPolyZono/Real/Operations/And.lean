import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE
import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
import CORALean.ContSet.Interval.Real.Operations.Point

/-!
# `ConPolyZono.and`

CORA's `@conPolyZono/and_`, and the reason a constrained representation exists:
two constrained polynomial zonotopes intersect to one, exactly.

The construction is `plus`'s plus one block of rows per coordinate saying the
two points agree, `Σ μ₁(α₁) G₁ − Σ μ₂(α₂) G₂ ∈ c₂ − c₁ + D`. Only the first
generator block survives — the second is pinned to it, kept at zero so the rows
have columns to read it in. Their coefficients are *monomials*, which is what a
`ConZonotope` cannot do, and `appendE` puts their exponent columns beside the
constraint ones. `D` is how far apart the two points may stand; `and` takes it
to be zero, and it is an argument because a float layer's nominal points differ
by whatever the two error boxes admit.

`and` runs `andDep` on the two `dependent` sets: an independent coefficient
answers to no constraint, so it could move the two points apart with nothing in
the system to forbid it. Freeing the independent blocks into factors first is
what makes this exact where CORA's `and_` encloses.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

/-- The row pinning the two points together in coordinate `i`, read against the
concatenated generator monomials. -/
def ConPolyZono.agreeRow (C₁ C₂ : ConPolyZono (Vec ℝ n)) (i : Fin n) :
    Fin (C₁.h + C₂.h) → ℝ :=
  Fin.append (fun l => C₁.G l i) fun l => -C₂.G l i

/-- The constraint matrix of `andDep`: the two systems block-diagonally over the
constraint columns and blind to the generator columns, then the agreement rows,
blind to the constraint columns. -/
def ConPolyZono.andA (C₁ C₂ : ConPolyZono (Vec ℝ n)) :
    Mat ℝ (C₁.m + C₂.m + n) (C₁.s + C₂.s + (C₁.h + C₂.h)) := fun i =>
  Fin.append
    (fun r => Fin.append (ConPolyZono.plusA C₁.A C₂.A r) (0 : Fin (C₁.h + C₂.h) → ℝ))
    (fun r => Fin.append (0 : Fin (C₁.s + C₂.s) → ℝ) (ConPolyZono.agreeRow C₁ C₂ r)) i

/-- The right-hand side of `andDep`: the two systems' own bounds, then the
agreement rows' `c₂ − c₁` widened by the tolerance. -/
def ConPolyZono.andB (C₁ C₂ : ConPolyZono (Vec ℝ n)) (D : Interval (Vec ℝ n)) :
    Interval (Vec ℝ (C₁.m + C₂.m + n)) :=
  ⟨Fin.append (ConPolyZono.plusB C₁.b C₂.b).inf fun i => C₂.c i - C₁.c i + D.inf i,
   Fin.append (ConPolyZono.plusB C₁.b C₂.b).sup fun i => C₂.c i - C₁.c i + D.sup i⟩

/-- Exact where both independent blocks are empty; `and` arranges that. `D` is
how far apart the two points may stand. -/
def ConPolyZono.andDep (C₁ C₂ : ConPolyZono (Vec ℝ n)) (D : Interval (Vec ℝ n)) :
    ConPolyZono (Vec ℝ n) where
  p := C₁.p + C₂.p
  h := C₁.h + C₂.h
  q := 0
  m := C₁.m + C₂.m + n
  s := C₁.s + C₂.s + (C₁.h + C₂.h)
  c := C₁.c
  G := Fin.append C₁.G 0
  E := PolyZonotope.plusE C₁.E C₂.E
  GI := Fin.elim0
  A := ConPolyZono.andA C₁ C₂
  b := ConPolyZono.andB C₁ C₂ D
  EC := ConPolyZono.appendE (PolyZonotope.plusE C₁.EC C₂.EC)
          (PolyZonotope.plusE C₁.E C₂.E)

/-- Zero tolerance: the two points agree exactly. -/
def ConPolyZono.and (C₁ C₂ : ConPolyZono (Vec ℝ n)) : ConPolyZono (Vec ℝ n) :=
  ConPolyZono.andDep C₁.dependent C₂.dependent (Interval.point 0)

theorem ConPolyZono.mulVec_andA_left (C₁ C₂ : ConPolyZono (Vec ℝ n))
    (v : Fin (C₁.s + C₂.s + (C₁.h + C₂.h)) → ℝ) (i : Fin (C₁.m + C₂.m)) :
    (ConPolyZono.andA C₁ C₂ *ᵥ v) (Fin.castAdd n i)
      = (ConPolyZono.plusA C₁.A C₂.A *ᵥ fun l => v (Fin.castAdd (C₁.h + C₂.h) l)) i := by
  show ∑ l : Fin (C₁.s + C₂.s + (C₁.h + C₂.h)),
      ConPolyZono.andA C₁ C₂ (Fin.castAdd n i) l * v l
    = ∑ l, ConPolyZono.plusA C₁.A C₂.A i l * v (Fin.castAdd (C₁.h + C₂.h) l)
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.andA, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero]

-- and the agreement rows, whose two blocks are the two generator matrices
theorem ConPolyZono.mulVec_andA_agree (C₁ C₂ : ConPolyZono (Vec ℝ n))
    (v : Fin (C₁.s + C₂.s + (C₁.h + C₂.h)) → ℝ) (i : Fin n) :
    (ConPolyZono.andA C₁ C₂ *ᵥ v) (Fin.natAdd (C₁.m + C₂.m) i)
      = (∑ l, C₁.G l i * v (Fin.natAdd (C₁.s + C₂.s) (Fin.castAdd C₂.h l)))
        - ∑ l, C₂.G l i * v (Fin.natAdd (C₁.s + C₂.s) (Fin.natAdd C₁.h l)) := by
  show ∑ l : Fin (C₁.s + C₂.s + (C₁.h + C₂.h)),
      ConPolyZono.andA C₁ C₂ (Fin.natAdd (C₁.m + C₂.m) i) l * v l = _
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.andA, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, zero_add]
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.agreeRow, Fin.append_left, Fin.append_right, neg_mul]
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg]

/-- What `andDep`'s constraint system says: each set's own constraints, and that
the two points agree coordinate by coordinate to within `D`. -/
theorem ConPolyZono.satisfies_andDep_iff (C₁ C₂ : ConPolyZono (Vec ℝ n))
    (D : Interval (Vec ℝ n)) (a : Fin (C₁.p + C₂.p) → ℝ) :
    (C₁.andDep C₂ D).satisfies a ↔
      (C₁.satisfies (fun k => a (Fin.castAdd C₂.p k))
        ∧ C₂.satisfies (fun k => a (Fin.natAdd C₁.p k)))
      ∧ ∀ i, C₂.c i - C₁.c i + D.inf i
            ≤ (∑ l, C₁.G l i
              * PolyZonotope.monomial C₁.E (fun k => a (Fin.castAdd C₂.p k)) l)
            - ∑ l, C₂.G l i
              * PolyZonotope.monomial C₂.E (fun k => a (Fin.natAdd C₁.p k)) l
          ∧ (∑ l, C₁.G l i
              * PolyZonotope.monomial C₁.E (fun k => a (Fin.castAdd C₂.p k)) l)
            - ∑ l, C₂.G l i
              * PolyZonotope.monomial C₂.E (fun k => a (Fin.natAdd C₁.p k)) l
          ≤ C₂.c i - C₁.c i + D.sup i := by
  have hcol : (fun l => PolyZonotope.monomial (ConPolyZono.appendE
        (PolyZonotope.plusE C₁.EC C₂.EC) (PolyZonotope.plusE C₁.E C₂.E)) a
          (Fin.castAdd (C₁.h + C₂.h) l))
      = PolyZonotope.monomial (PolyZonotope.plusE C₁.EC C₂.EC) a :=
    funext fun l => ConPolyZono.monomial_appendE_left _ _ a l
  -- the inherited rows first: through the append they are `plusA` on the left block
  have hC : ∀ i : Fin (C₁.m + C₂.m),
      (ConPolyZono.andA C₁ C₂ *ᵥ PolyZonotope.monomial (ConPolyZono.appendE
          (PolyZonotope.plusE C₁.EC C₂.EC) (PolyZonotope.plusE C₁.E C₂.E)) a)
          (Fin.castAdd n i)
        = (ConPolyZono.plusA C₁.A C₂.A *ᵥ
            PolyZonotope.monomial (PolyZonotope.plusE C₁.EC C₂.EC) a) i := by
    intro i
    rw [ConPolyZono.mulVec_andA_left, hcol]
  -- then the agreement rows, each side's monomials read off its own factors
  have hG : ∀ i : Fin n,
      (ConPolyZono.andA C₁ C₂ *ᵥ PolyZonotope.monomial (ConPolyZono.appendE
          (PolyZonotope.plusE C₁.EC C₂.EC) (PolyZonotope.plusE C₁.E C₂.E)) a)
          (Fin.natAdd (C₁.m + C₂.m) i)
        = (∑ l, C₁.G l i
              * PolyZonotope.monomial C₁.E (fun k => a (Fin.castAdd C₂.p k)) l)
            - ∑ l, C₂.G l i
              * PolyZonotope.monomial C₂.E (fun k => a (Fin.natAdd C₁.p k)) l := by
    intro i
    rw [ConPolyZono.mulVec_andA_agree]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by
        rw [ConPolyZono.monomial_appendE_right, PolyZonotope.monomial_plusE_left]
    · exact Finset.sum_congr rfl fun l _ => by
        rw [ConPolyZono.monomial_appendE_right, PolyZonotope.monomial_plusE_right]
  constructor
  · intro hsat'
    -- the projections are read away first: `Fin.castAdd` does not fit `Fin (andDep ..).m`
    have hsat : ConPolyZono.holds (ConPolyZono.andA C₁ C₂) (ConPolyZono.andB C₁ C₂ D)
        (ConPolyZono.appendE (PolyZonotope.plusE C₁.EC C₂.EC)
          (PolyZonotope.plusE C₁.E C₂.E)) a := hsat'
    refine ⟨(ConPolyZono.holds_plus_iff C₁.A C₁.b C₁.EC C₂.A C₂.b C₂.EC a).mp
        (fun i => ?_), fun i => ?_⟩
    · have h := hsat (Fin.castAdd n i)
      rw [hC i] at h
      simpa only [ConPolyZono.andB, Fin.append_left] using h
    · have h := hsat (Fin.natAdd (C₁.m + C₂.m) i)
      rw [hG i] at h
      simpa only [ConPolyZono.andB, Fin.append_right] using h
  · rintro ⟨hcon, hagree⟩
    have hplus := (ConPolyZono.holds_plus_iff C₁.A C₁.b C₁.EC C₂.A C₂.b C₂.EC a).mpr hcon
    -- through the projections the index reads `Fin (andDep ..).m`, which `Fin.castAdd` misses
    show ConPolyZono.holds (ConPolyZono.andA C₁ C₂) (ConPolyZono.andB C₁ C₂ D)
      (ConPolyZono.appendE (PolyZonotope.plusE C₁.EC C₂.EC)
        (PolyZonotope.plusE C₁.E C₂.E)) a
    refine Fin.addCases (fun i => ?_) fun i => ?_
    · rw [hC i]
      simpa only [ConPolyZono.andB, Fin.append_left] using hplus i
    · rw [hG i]
      simpa only [ConPolyZono.andB, Fin.append_right] using hagree i

end CORALean.Real
