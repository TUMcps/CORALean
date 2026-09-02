import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
import CORALean.ContSet.PolyZonotope.Real.Operations.Plus

/-!
# `ConPolyZono.plus`

CORA's `@conPolyZono/plus`: `PolyZonotope.plus` with the two constraint systems
carried along side by side.

Nothing couples the two sets, so nothing may be identified: the factors are laid
out block-diagonally by `PolyZonotope.plusE`, and the constraint *rows* are laid
out block-diagonally too, by `plusA`. A row of one set then reads exponent zero
on every factor of the other, so it constrains the factors it came with and no
others — which is what makes the sum exact rather than too small.

`plusA` is the one place a matrix is still assembled by hand. It has to be: the
constraints of the two sets meet in one matrix, and there is no polytope here to
pull back along a projection the way `ConZonotope.plus` does.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- Two constraint systems side by side, block-diagonally: each set's rows read
only its own constraint generators. -/
def ConPolyZono.plusA {m₁ s₁ m₂ s₂ : ℕ} (A₁ : Mat ℝ m₁ s₁) (A₂ : Mat ℝ m₂ s₂) :
    Mat ℝ (m₁ + m₂) (s₁ + s₂) := fun i =>
  Fin.append (fun r => Fin.append (A₁ r) (0 : Fin s₂ → ℝ))
    (fun r => Fin.append (0 : Fin s₁ → ℝ) (A₂ r)) i

def ConPolyZono.plus (C₁ C₂ : ConPolyZono α) : ConPolyZono α where
  p := C₁.p + C₂.p
  h := C₁.h + C₂.h
  q := C₁.q + C₂.q
  m := C₁.m + C₂.m
  s := C₁.s + C₂.s
  c := C₁.c + C₂.c
  G := Fin.append C₁.G C₂.G
  E := PolyZonotope.plusE C₁.E C₂.E
  GI := Fin.append C₁.GI C₂.GI
  A := ConPolyZono.plusA C₁.A C₂.A
  b := Fin.append C₁.b C₂.b
  EC := PolyZonotope.plusE C₁.EC C₂.EC

theorem ConPolyZono.mulVec_plusA_left {m₁ s₁ m₂ s₂ : ℕ} (A₁ : Mat ℝ m₁ s₁)
    (A₂ : Mat ℝ m₂ s₂) (v : Fin (s₁ + s₂) → ℝ) (i : Fin m₁) :
    (ConPolyZono.plusA A₁ A₂ *ᵥ v) (Fin.castAdd m₂ i)
      = (A₁ *ᵥ fun l => v (Fin.castAdd s₂ l)) i := by
  show ∑ l : Fin (s₁ + s₂), ConPolyZono.plusA A₁ A₂ (Fin.castAdd m₂ i) l * v l
      = ∑ l, A₁ i l * v (Fin.castAdd s₂ l)
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.plusA, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero]

theorem ConPolyZono.mulVec_plusA_right {m₁ s₁ m₂ s₂ : ℕ} (A₁ : Mat ℝ m₁ s₁)
    (A₂ : Mat ℝ m₂ s₂) (v : Fin (s₁ + s₂) → ℝ) (i : Fin m₂) :
    (ConPolyZono.plusA A₁ A₂ *ᵥ v) (Fin.natAdd m₁ i)
      = (A₂ *ᵥ fun l => v (Fin.natAdd s₁ l)) i := by
  show ∑ l : Fin (s₁ + s₂), ConPolyZono.plusA A₁ A₂ (Fin.natAdd m₁ i) l * v l
      = ∑ l, A₂ i l * v (Fin.natAdd s₁ l)
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.plusA, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, zero_add]

/-- Two constraint systems side by side hold exactly when each holds on the
factors it came with. The block-diagonal exponent matrix is what makes the
right-to-left direction work: neither system's monomials see the other's
factors. -/
theorem ConPolyZono.holds_plus_iff {p₁ p₂ m₁ s₁ m₂ s₂ : ℕ} (A₁ : Mat ℝ m₁ s₁)
    (b₁ : Vec ℝ m₁) (EC₁ : Fin p₁ → Fin s₁ → ℕ) (A₂ : Mat ℝ m₂ s₂) (b₂ : Vec ℝ m₂)
    (EC₂ : Fin p₂ → Fin s₂ → ℕ) (a : Fin (p₁ + p₂) → ℝ) :
    ConPolyZono.holds (ConPolyZono.plusA A₁ A₂) (Fin.append b₁ b₂)
        (PolyZonotope.plusE EC₁ EC₂) a
      ↔ ConPolyZono.holds A₁ b₁ EC₁ (fun k => a (Fin.castAdd p₂ k))
        ∧ ConPolyZono.holds A₂ b₂ EC₂ (fun k => a (Fin.natAdd p₁ k)) := by
  have hL : ∀ i : Fin m₁,
      (ConPolyZono.plusA A₁ A₂ *ᵥ PolyZonotope.monomial (PolyZonotope.plusE EC₁ EC₂) a)
          (Fin.castAdd m₂ i)
        = (A₁ *ᵥ PolyZonotope.monomial EC₁ fun k => a (Fin.castAdd p₂ k)) i := by
    intro i
    have hm : (fun l => PolyZonotope.monomial (PolyZonotope.plusE EC₁ EC₂) a
          (Fin.castAdd s₂ l))
        = PolyZonotope.monomial EC₁ (fun k => a (Fin.castAdd p₂ k)) :=
      funext fun l => PolyZonotope.monomial_plusE_left EC₁ EC₂ a l
    rw [ConPolyZono.mulVec_plusA_left, hm]
  have hR : ∀ i : Fin m₂,
      (ConPolyZono.plusA A₁ A₂ *ᵥ PolyZonotope.monomial (PolyZonotope.plusE EC₁ EC₂) a)
          (Fin.natAdd m₁ i)
        = (A₂ *ᵥ PolyZonotope.monomial EC₂ fun k => a (Fin.natAdd p₁ k)) i := by
    intro i
    have hm : (fun l => PolyZonotope.monomial (PolyZonotope.plusE EC₁ EC₂) a
          (Fin.natAdd s₁ l))
        = PolyZonotope.monomial EC₂ (fun k => a (Fin.natAdd p₁ k)) :=
      funext fun l => PolyZonotope.monomial_plusE_right EC₁ EC₂ a l
    rw [ConPolyZono.mulVec_plusA_right, hm]
  constructor
  · intro hsat
    exact ⟨fun i => (hL i).symm.trans
        ((hsat (Fin.castAdd m₂ i)).trans (Fin.append_left b₁ b₂ i)),
      fun i => (hR i).symm.trans
        ((hsat (Fin.natAdd m₁ i)).trans (Fin.append_right b₁ b₂ i))⟩
  · rintro ⟨h₁, h₂⟩
    show ∀ i, (ConPolyZono.plusA A₁ A₂ *ᵥ
        PolyZonotope.monomial (PolyZonotope.plusE EC₁ EC₂) a) i = Fin.append b₁ b₂ i
    refine Fin.addCases (fun i => ?_) fun i => ?_
    · rw [hL i, Fin.append_left]
      exact h₁ i
    · rw [hR i, Fin.append_right]
      exact h₂ i

omit [Module ℝ α] in
/-- The same at a sum, where the two systems are the two sets'. -/
theorem ConPolyZono.satisfies_plus_iff (C₁ C₂ : ConPolyZono α)
    (a : Fin (C₁.p + C₂.p) → ℝ) :
    (C₁.plus C₂).satisfies a ↔
      C₁.satisfies (fun k => a (Fin.castAdd C₂.p k))
        ∧ C₂.satisfies (fun k => a (Fin.natAdd C₁.p k)) :=
  ConPolyZono.holds_plus_iff C₁.A C₁.b C₁.EC C₂.A C₂.b C₂.EC a

end CORALean.Real
