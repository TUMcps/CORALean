import CORALean.Global.Entrywise

/-!
# Sparse polynomial zonotopes: the representation

Kochdumper and Althoff, *Sparse Polynomial Zonotopes* (2021), and CORA's
`polyZonotope`: a centre, dependent generators `G` scaled by monomials in
factors `α ∈ [-1,1]ᵖ` read off the exponent matrix `E`, and independent
generators `GI` scaled by their own `β ∈ [-1,1]ᵍ`.

What makes the representation more than a zonotope is that the `α` are *shared*:
the same factor multiplies every generator whose exponent row is nonzero, so the
denoted set is generally neither convex nor a zonotope, and a quadratic map
stays inside the class.

`E` is a family `Fin p → Fin h → ℕ`, one row per factor and one column per
generator, as in the paper. The sparsity of the paper's title is a property of
how `E` is stored, not of what it denotes, so nothing here mentions it.

CORA carries an identifier vector `id` naming each factor, so that two sets
sharing a factor keep it identified. Here identity is positional instead — a
factor *is* its row index — which is why `plus` has to lay the two exponent
matrices out block-diagonally rather than overlay them.

Over any real module, as `Zonotope` is: a monomial is a scalar, and nothing
about scaling a generator by one needs coordinates.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

structure PolyZonotope (α : Type) where
  /-- The dependent factors, shared across all of `G`. -/
  p : ℕ
  /-- The dependent generators. -/
  h : ℕ
  /-- The independent generators. -/
  q : ℕ
  c : α
  G : Fin h → α
  E : Fin p → Fin h → ℕ
  GI : Fin q → α

/-- The monomial `∏ₖ αₖ^{E[k,i]}` scaling dependent generator `i`. Stated over an
exponent matrix rather than over a set, so an operation can name the monomials of
the matrix it is still assembling. -/
def PolyZonotope.monomial {p h : ℕ} (E : Fin p → Fin h → ℕ) (a : Fin p → ℝ)
    (i : Fin h) : ℝ := ∏ k, a k ^ E k i

def PolyZonotope.construct (PZ : PolyZonotope α) : Set α :=
  {x | ∃ a : Fin PZ.p → ℝ, ∃ β : Fin PZ.q → ℝ, (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ x = PZ.c + ∑ i, PolyZonotope.monomial PZ.E a i • PZ.G i + ∑ j, β j • PZ.GI j}

/-- A monomial never leaves `[-1,1]`, which is what lets every dependent
generator be read as an independent one. The enclosing conversions all rest on
this line. -/
theorem PolyZonotope.abs_monomial_le_one {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1) (i : Fin h) :
    |PolyZonotope.monomial E a i| ≤ 1 := by
  rw [PolyZonotope.monomial, Finset.abs_prod]
  refine Finset.prod_le_one (fun k _ => abs_nonneg _) fun k _ => ?_
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (ha k)

/-- Every factor at exponent zero, so the monomial is `1`: the shape a
concatenation gives the generators it did not come from. -/
theorem PolyZonotope.monomial_zero {p h : ℕ} {E : Fin p → Fin h → ℕ} (a : Fin p → ℝ)
    {i : Fin h} (hE : ∀ k, E k i = 0) : PolyZonotope.monomial E a i = 1 := by
  rw [PolyZonotope.monomial]
  exact Finset.prod_eq_one fun k _ => by rw [hE k, pow_zero]

/-- Exponent columns add where monomials multiply, which is what keeps the
representation closed under a quadratic map. -/
theorem PolyZonotope.monomial_add {p h : ℕ} (E₁ E₂ : Fin p → Fin h → ℕ) (a : Fin p → ℝ)
    (i : Fin h) :
    PolyZonotope.monomial (fun k i => E₁ k i + E₂ k i) a i
      = PolyZonotope.monomial E₁ a i * PolyZonotope.monomial E₂ a i := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial, PolyZonotope.monomial,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => pow_add (a k) (E₁ k i) (E₂ k i)

/-- The identity exponent matrix: factor `i` appears in generator `i` alone and
to the first power, so its monomial is the factor itself. That is what a free
coefficient looks like once it is dependent — a zonotope's whole exponent
matrix, and the block `dependent` appends. -/
def PolyZonotope.identE (m : ℕ) : Fin m → Fin m → ℕ := fun k i => if k = i then 1 else 0

theorem PolyZonotope.monomial_identE {m : ℕ} (a : Fin m → ℝ) (i : Fin m) :
    PolyZonotope.monomial (PolyZonotope.identE m) a i = a i := by
  rw [PolyZonotope.monomial, Finset.prod_eq_single i]
  · have h1 : PolyZonotope.identE m i i = 1 := if_pos rfl
    rw [h1, pow_one]
  · intro k _ hk
    have h0 : PolyZonotope.identE m k i = 0 := if_neg hk
    rw [h0, pow_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The same membership read coordinatewise, which is the form the operations
that need coordinates are stated in. The scalar sits on the right of each
generator entry, as it does for `Zonotope`. -/
theorem PolyZonotope.mem_construct_iff {n : ℕ} {PZ : PolyZonotope (Vec ℝ n)} {x : Vec ℝ n} :
    x ∈ PZ.construct ↔
      ∃ a : Fin PZ.p → ℝ, ∃ β : Fin PZ.q → ℝ, (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ ∀ i, x i = PZ.c i + (∑ l, PZ.G l i * PolyZonotope.monomial PZ.E a l)
              + ∑ j, PZ.GI j i * β j := by
  have key : ∀ (a : Fin PZ.p → ℝ) (β : Fin PZ.q → ℝ) (i : Fin n),
      (PZ.c + ∑ l, PolyZonotope.monomial PZ.E a l • PZ.G l + ∑ j, β j • PZ.GI j) i
        = PZ.c i + (∑ l, PZ.G l i * PolyZonotope.monomial PZ.E a l)
            + ∑ j, PZ.GI j i * β j := by
    intro a β i
    rw [Pi.add_apply, Entrywise.add_sum_smul_apply, Finset.sum_apply]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => by
      rw [Pi.smul_apply, smul_eq_mul, mul_comm])
  constructor
  · rintro ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, key a β⟩
  · rintro ⟨a, β, ha, hβ, hx⟩
    exact ⟨a, β, ha, hβ, funext fun i => (hx i).trans (key a β i).symm⟩

end CORALean.Real
