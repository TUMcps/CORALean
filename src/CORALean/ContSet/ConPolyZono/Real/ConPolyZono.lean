import CORALean.ContSet.Interval.Real.Interval
import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# Constrained polynomial zonotopes: the representation

CORA's `conPolyZono` [1]: a `PolyZonotope` whose factors additionally satisfy
polynomial constraints `A μ(α) ∈ b`, the constraint monomials read off `EC` over
the *same* factors as the generators. That sharing is the content of the
representation — a constraint and a generator are two readings of one
`PolyZonotope.monomial` — so the constraints are a matrix relation, not a polytope.

`b` is an `Interval` where [1] writes `A μ(α) = b`: an equality has no direction
to round in, so no float layer could compute a constraint at all; `Interval.point
b` gives it back. Of the five counts two are renamed against [1] to avoid
`PolyZonotope`'s: `m` counts constraints, `s` constraint generators. `holds`
states the constraint over the data, which an operation assembling one needs.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

structure ConPolyZono (α : Type) where
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
  c : α
  G : Fin h → α
  E : Fin p → Fin h → ℕ
  GI : Fin q → α
  A : Mat ℝ m s
  /-- Interval-valued, so that a bound has a direction to be rounded in. -/
  b : Interval (Vec ℝ m)
  EC : Fin p → Fin s → ℕ

/-- The constraint `A μ(α) ∈ b`, one row at a time and over the data rather than
over a set, so an operation can name the constraints of the system it is still
assembling. -/
def ConPolyZono.holds {p m s : ℕ} (A : Mat ℝ m s) (b : Interval (Vec ℝ m))
    (EC : Fin p → Fin s → ℕ) (a : Fin p → ℝ) : Prop :=
  ∀ i, b.inf i ≤ (A *ᵥ PolyZonotope.monomial EC a) i
        ∧ (A *ᵥ PolyZonotope.monomial EC a) i ≤ b.sup i

/-- The paper's equality, as the degenerate interval. -/
theorem ConPolyZono.holds_point_iff {p m s : ℕ} (A : Mat ℝ m s) (b : Vec ℝ m)
    (EC : Fin p → Fin s → ℕ) (a : Fin p → ℝ) :
    ConPolyZono.holds A (Interval.point b) EC a
      ↔ ∀ i, (A *ᵥ PolyZonotope.monomial EC a) i = b i :=
  forall_congr' fun _ => ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/-- Widening a bound only admits more factor vectors, which is what makes a
rounded constraint sound. -/
theorem ConPolyZono.holds_mono {p m s : ℕ} {A : Mat ℝ m s} {b b' : Interval (Vec ℝ m)}
    {EC : Fin p → Fin s → ℕ} {a : Fin p → ℝ} (hinf : ∀ i, b'.inf i ≤ b.inf i)
    (hsup : ∀ i, b.sup i ≤ b'.sup i) (h : ConPolyZono.holds A b EC a) :
    ConPolyZono.holds A b' EC a :=
  fun i => ⟨le_trans (hinf i) (h i).1, le_trans (h i).2 (hsup i)⟩

/-- The constraint reads its data only through the vector `A μ(α)`, so a
rewriting of the constraint block that leaves that vector alone leaves the
constraint alone — which is what compacting `A` and `EC` does. -/
theorem ConPolyZono.holds_congr {p p' m s s' : ℕ} {A : Mat ℝ m s} {A' : Mat ℝ m s'}
    {b : Interval (Vec ℝ m)} {EC : Fin p → Fin s → ℕ} {EC' : Fin p' → Fin s' → ℕ}
    {a : Fin p → ℝ} {a' : Fin p' → ℝ}
    (h : A' *ᵥ PolyZonotope.monomial EC' a' = A *ᵥ PolyZonotope.monomial EC a) :
    ConPolyZono.holds A b EC a ↔ ConPolyZono.holds A' b EC' a' := by
  rw [ConPolyZono.holds, ConPolyZono.holds, h]

/-- What a set's own factors must satisfy. -/
def ConPolyZono.satisfies (C : ConPolyZono α) (a : Fin C.p → ℝ) : Prop :=
  ConPolyZono.holds C.A C.b C.EC a

def ConPolyZono.construct (C : ConPolyZono α) : Set α :=
  {x | ∃ a : Fin C.p → ℝ, ∃ β : Fin C.q → ℝ, (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ C.satisfies a
        ∧ x = C.c + ∑ i, PolyZonotope.monomial C.E a i • C.G i + ∑ j, β j • C.GI j}

/-- An exponent matrix widened by fresh factors that none of its monomials uses:
what a constraint block keeps when an operation adds factors beside the ones it
was written against. -/
def ConPolyZono.padE {p s : ℕ} (EC : Fin p → Fin s → ℕ) (r : ℕ) :
    Fin (p + r) → Fin s → ℕ :=
  Fin.append EC fun _ _ => 0

/-- Two exponent matrices over the *same* factors, side by side, which is what
an intersection has to do. Not `PolyZonotope.plusE`, which puts two *factor*
sets side by side and would decouple the very columns this couples. -/
def ConPolyZono.appendE {p s t : ℕ} (E₁ : Fin p → Fin s → ℕ) (E₂ : Fin p → Fin t → ℕ) :
    Fin p → Fin (s + t) → ℕ :=
  fun k => Fin.append (E₁ k) (E₂ k)

theorem ConPolyZono.monomial_padE {p s : ℕ} (EC : Fin p → Fin s → ℕ) (r : ℕ)
    (a : Fin (p + r) → ℝ) (l : Fin s) :
    PolyZonotope.monomial (ConPolyZono.padE EC r) a l
      = PolyZonotope.monomial EC (fun k => a (Fin.castAdd r k)) l := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add]
  have hnew : (∏ k : Fin r, a (Fin.natAdd p k)
      ^ ConPolyZono.padE EC r (Fin.natAdd p k) l) = 1 :=
    Finset.prod_eq_one fun k _ => by
      simp only [ConPolyZono.padE, Fin.append_right, pow_zero]
  have hold : (∏ k : Fin p, a (Fin.castAdd r k)
      ^ ConPolyZono.padE EC r (Fin.castAdd r k) l)
      = ∏ k, a (Fin.castAdd r k) ^ EC k l :=
    Finset.prod_congr rfl fun k _ => by
      simp only [ConPolyZono.padE, Fin.append_left]
  rw [hnew, hold, mul_one]

-- a monomial read back off each half of the append, the factors being shared
theorem ConPolyZono.monomial_appendE_left {p s t : ℕ} (E₁ : Fin p → Fin s → ℕ)
    (E₂ : Fin p → Fin t → ℕ) (a : Fin p → ℝ) (l : Fin s) :
    PolyZonotope.monomial (ConPolyZono.appendE E₁ E₂) a (Fin.castAdd t l)
      = PolyZonotope.monomial E₁ a l := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial]
  exact Finset.prod_congr rfl fun k _ => by
    simp only [ConPolyZono.appendE, Fin.append_left]

theorem ConPolyZono.monomial_appendE_right {p s t : ℕ} (E₁ : Fin p → Fin s → ℕ)
    (E₂ : Fin p → Fin t → ℕ) (a : Fin p → ℝ) (l : Fin t) :
    PolyZonotope.monomial (ConPolyZono.appendE E₁ E₂) a (Fin.natAdd s l)
      = PolyZonotope.monomial E₂ a l := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial]
  exact Finset.prod_congr rfl fun k _ => by
    simp only [ConPolyZono.appendE, Fin.append_right]

/-- The same membership read coordinatewise, which is the form the operations
that need coordinates are stated in. The scalar sits on the right of each
generator entry, as it does for `PolyZonotope`. -/
theorem ConPolyZono.mem_construct_iff {n : ℕ} {C : ConPolyZono (Vec ℝ n)} {x : Vec ℝ n} :
    x ∈ C.construct ↔
      ∃ a : Fin C.p → ℝ, ∃ β : Fin C.q → ℝ, (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ C.satisfies a
        ∧ ∀ i, x i = C.c i + (∑ l, C.G l i * PolyZonotope.monomial C.E a l)
              + ∑ j, C.GI j i * β j := by
  have key : ∀ (a : Fin C.p → ℝ) (β : Fin C.q → ℝ) (i : Fin n),
      (C.c + ∑ l, PolyZonotope.monomial C.E a l • C.G l + ∑ j, β j • C.GI j) i
        = C.c i + (∑ l, C.G l i * PolyZonotope.monomial C.E a l)
            + ∑ j, C.GI j i * β j := by
    intro a β i
    rw [Pi.add_apply, Entrywise.add_sum_smul_apply, Finset.sum_apply]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => by
      rw [Pi.smul_apply, smul_eq_mul, mul_comm])
  constructor
  · rintro ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨a, β, ha, hβ, hsat, key a β⟩
  · rintro ⟨a, β, ha, hβ, hsat, hx⟩
    exact ⟨a, β, ha, hβ, hsat, funext fun i => (hx i).trans (key a β i).symm⟩

end CORALean.Real
