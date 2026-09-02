import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# Constrained polynomial zonotopes: the representation

Kochdumper and Althoff, *Constrained Polynomial Zonotopes* (2020), and CORA's
`conPolyZono`: a `PolyZonotope` whose dependent factors additionally have to
satisfy polynomial equalities `A μ(α) = b`, the constraint monomials `μ` read
off `EC` over the *same* factors `α` as the generators.

That sharing is the whole content of the representation, as factor sharing is
for the unconstrained one, and it is why the monomial here is
`PolyZonotope.monomial` rather than a second copy: a constraint and a generator
are two readings of one monomial in one set of factors.

The constraint is a matrix equation, as in the paper and in CORA, and *not* an
`HPolytope` the way `ConZonotope` carries its constraints. A polytope over the
factors could not say what a polynomial equality says — the constraint is
polynomial in `α`, not linear — and a polytope over the monomials would let them
move independently of the factors they are built from, which is exactly the
coupling the representation exists to record.

Equalities only, again as in the paper. `ConZonotope` admits inequalities
because a halfspace description carries both at no cost; here an inequality
would need a slack factor together with a bound on it, so it is left out rather
than faked.

`holds` states the constraint over the data rather than over a set, as
`monomial` is stated over an exponent matrix: an operation concatenating two
constraint systems has to name the system it is still assembling, whose counts
are not yet a projection of anything.

Five counts, and the paper's names collide with `PolyZonotope`'s twice over, so
two are renamed: `m` is the number of constraints and `s` the number of
constraint generators, the paper's `q` for the latter being already taken by the
independent generators.

Over any real module, as `PolyZonotope` is: the constraint lives on the factors
whatever the generators point into.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
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
  b : Vec ℝ m
  EC : Fin p → Fin s → ℕ

/-- The constraint `A μ(α) = b`, one row at a time and over the data rather than
over a set, so an operation can name the constraints of the system it is still
assembling. -/
def ConPolyZono.holds {p m s : ℕ} (A : Mat ℝ m s) (b : Vec ℝ m)
    (EC : Fin p → Fin s → ℕ) (a : Fin p → ℝ) : Prop :=
  ∀ i, (A *ᵥ PolyZonotope.monomial EC a) i = b i

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

/-- Two exponent matrices over the *same* factors, side by side: constraint
monomials and generator monomials read off one matrix, which is what an
intersection has to do. Not `PolyZonotope.plusE`, which puts two *factor* sets
side by side and would decouple the very columns this couples. -/
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
