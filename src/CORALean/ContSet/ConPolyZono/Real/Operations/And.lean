import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Real.Operations.Plus

/-!
# `ConPolyZono.and`

CORA's `@conPolyZono/and_`, and the reason a constrained representation exists:
the intersection of two constrained polynomial zonotopes is one, exactly.
Nothing else in this repository intersects a non-convex set without loss.

The construction is `plus`'s, plus one block of rows. Factors, generators and
constraint systems all concatenate as they do for a sum; what intersection adds
is `n` rows saying the two points agree,

  `Σ μ₁(α₁) G₁ − Σ μ₂(α₂) G₂ = c₂ − c₁`,

one per coordinate. Only the first generator block then survives — the second is
pinned to it, and is kept at zero rather than dropped so that the agreement rows
have columns to read it in.

Those rows are where the representation does something a `ConZonotope` cannot:
their coefficients are *monomials*, so the constraint they impose is polynomial
in the factors, and the exponent columns they need are exactly the generators'
own. `appendE` puts them beside the constraint columns, over the same factors.

`and` runs `andDep` on the two `dependent` sets, as `PolyZonotope.quadMap` runs
`quadMapDep`. It has to: the agreement rows constrain the factors, and an
independent coefficient is not one — an independent generator could move the two
points apart with nothing in the system to forbid it. `andDep` alone is
therefore exact only where both independent blocks are empty, and its theorem
says so.

At `Vec` only, since the agreement rows read a generator coordinate by
coordinate.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
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

/-- Exact where both independent blocks are empty; `and` arranges that. -/
def ConPolyZono.andDep (C₁ C₂ : ConPolyZono (Vec ℝ n)) : ConPolyZono (Vec ℝ n) where
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
  b := Fin.append (Fin.append C₁.b C₂.b) fun i => C₂.c i - C₁.c i
  EC := ConPolyZono.appendE (PolyZonotope.plusE C₁.EC C₂.EC)
          (PolyZonotope.plusE C₁.E C₂.E)

def ConPolyZono.and (C₁ C₂ : ConPolyZono (Vec ℝ n)) : ConPolyZono (Vec ℝ n) :=
  ConPolyZono.andDep C₁.dependent C₂.dependent

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
the two points agree coordinate by coordinate. -/
theorem ConPolyZono.satisfies_andDep_iff (C₁ C₂ : ConPolyZono (Vec ℝ n))
    (a : Fin (C₁.p + C₂.p) → ℝ) :
    (C₁.andDep C₂).satisfies a ↔
      (C₁.satisfies (fun k => a (Fin.castAdd C₂.p k))
        ∧ C₂.satisfies (fun k => a (Fin.natAdd C₁.p k)))
      ∧ ∀ i, (∑ l, C₁.G l i
              * PolyZonotope.monomial C₁.E (fun k => a (Fin.castAdd C₂.p k)) l)
            - ∑ l, C₂.G l i
              * PolyZonotope.monomial C₂.E (fun k => a (Fin.natAdd C₁.p k)) l
          = C₂.c i - C₁.c i := by
  have hcol : (fun l => PolyZonotope.monomial (ConPolyZono.appendE
        (PolyZonotope.plusE C₁.EC C₂.EC) (PolyZonotope.plusE C₁.E C₂.E)) a
          (Fin.castAdd (C₁.h + C₂.h) l))
      = PolyZonotope.monomial (PolyZonotope.plusE C₁.EC C₂.EC) a :=
    funext fun l => ConPolyZono.monomial_appendE_left _ _ a l
  have hC : ∀ i : Fin (C₁.m + C₂.m),
      (ConPolyZono.andA C₁ C₂ *ᵥ PolyZonotope.monomial (ConPolyZono.appendE
          (PolyZonotope.plusE C₁.EC C₂.EC) (PolyZonotope.plusE C₁.E C₂.E)) a)
          (Fin.castAdd n i)
        = (ConPolyZono.plusA C₁.A C₂.A *ᵥ
            PolyZonotope.monomial (PolyZonotope.plusE C₁.EC C₂.EC) a) i := by
    intro i
    rw [ConPolyZono.mulVec_andA_left, hcol]
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
  · intro hsat
    refine ⟨(ConPolyZono.holds_plus_iff C₁.A C₁.b C₁.EC C₂.A C₂.b C₂.EC a).mp
        (fun i => ?_), fun i => ?_⟩
    -- the right-hand vector is spelt out: the expected type reads `b` off the
    -- structure, so unification has nothing to read the second block from
    · exact (hC i).symm.trans ((hsat (Fin.castAdd n i)).trans
        (Fin.append_left (Fin.append C₁.b C₂.b) (fun j => C₂.c j - C₁.c j) i))
    · exact (hG i).symm.trans ((hsat (Fin.natAdd (C₁.m + C₂.m) i)).trans
        (Fin.append_right (Fin.append C₁.b C₂.b) (fun j => C₂.c j - C₁.c j) i))
  · rintro ⟨hcon, hagree⟩
    have hplus := (ConPolyZono.holds_plus_iff C₁.A C₁.b C₁.EC C₂.A C₂.b C₂.EC a).mpr hcon
    show ∀ i, (ConPolyZono.andA C₁ C₂ *ᵥ PolyZonotope.monomial (ConPolyZono.appendE
        (PolyZonotope.plusE C₁.EC C₂.EC) (PolyZonotope.plusE C₁.E C₂.E)) a) i
      = Fin.append (Fin.append C₁.b C₂.b) (fun i => C₂.c i - C₁.c i) i
    refine Fin.addCases (fun i => ?_) fun i => ?_
    · rw [hC i, Fin.append_left]
      exact hplus i
    · rw [hG i, Fin.append_right]
      exact hagree i

end CORALean.Real
