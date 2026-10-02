import CORALean.Global.Tensor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
# Taylor models: the representation

CORA's `taylm` (`contSet/@taylm/taylm.m`): a polynomial `p` in `n` variables and a
remainder interval `[remInf, remSup]`, read over CORA's normalized domain, the box
`[-1, 1]ⁿ` (`box`). CORA stores no domain: its constructor maps a variable's interval
onto `[-1, 1]` (`mid + rad · t`), and every range bound it computes (`interval`) assumes
that box. So does this one.

A term is a coefficient and an exponent vector; the polynomial is a list of them, unsorted
and possibly repeating an exponent. Identity of variables is positional, `Fin n`, where CORA
matches them by name (`priv_rescale_dim`).

What it means is functional: `T.Encloses f` says `f t - p t ∈ [remInf, remSup]` on the
box. That is what CORA's arithmetic is sound for: `times` and the elementary functions
are statements about the function the model encloses, not about its range set, which loses
the shared variables. `construct` is the range set of an array of models over the same
variables, CORA's `[p₁(t) + e₁; …]` with `t ∈ [-1, 1]ⁿ`, for the conversions.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Taylm (n : ℕ) where
  terms : List (ℝ × (Fin n → ℕ))
  remInf : ℝ
  remSup : ℝ
  /-- The order `times` truncates to, CORA's `max_order`. -/
  maxOrder : ℕ

/-- CORA's normalized domain. -/
def Taylm.box (n : ℕ) : Set (Vec ℝ n) := {t | ∀ k, |t k| ≤ 1}

def Taylm.monomial (e : Fin n → ℕ) (t : Vec ℝ n) : ℝ := ∏ k, t k ^ e k

/-- A term list evaluated, stated over the list so an operation can name the value of a
list it is still assembling. -/
def Taylm.polyOf (L : List (ℝ × (Fin n → ℕ))) (t : Vec ℝ n) : ℝ :=
  (L.map fun a => a.1 * Taylm.monomial a.2 t).sum

def Taylm.poly (T : Taylm n) (t : Vec ℝ n) : ℝ := Taylm.polyOf T.terms t

/-- The functional semantics: `f` minus the polynomial stays in the remainder on the box. -/
def Taylm.Encloses (T : Taylm n) (f : Vec ℝ n → ℝ) : Prop :=
  ∀ t ∈ Taylm.box n, T.remInf ≤ f t - T.poly t ∧ f t - T.poly t ≤ T.remSup

/-- The range set of an array of models sharing their variables. -/
def Taylm.construct {m : ℕ} (T : Fin m → Taylm n) : Set (Vec ℝ m) :=
  {x | ∃ t ∈ Taylm.box n, ∀ i,
    (T i).remInf ≤ x i - (T i).poly t ∧ x i - (T i).poly t ≤ (T i).remSup}

/-! ## Evaluating a term list

What every operation's proof reads its polynomial through. -/

@[simp] theorem Taylm.polyOf_nil (t : Vec ℝ n) : Taylm.polyOf [] t = 0 := rfl

@[simp] theorem Taylm.polyOf_cons (a : ℝ × (Fin n → ℕ)) (L : List (ℝ × (Fin n → ℕ)))
    (t : Vec ℝ n) :
    Taylm.polyOf (a :: L) t = a.1 * Taylm.monomial a.2 t + Taylm.polyOf L t := by
  simp [Taylm.polyOf]

theorem Taylm.polyOf_append (L₁ L₂ : List (ℝ × (Fin n → ℕ))) (t : Vec ℝ n) :
    Taylm.polyOf (L₁ ++ L₂) t = Taylm.polyOf L₁ t + Taylm.polyOf L₂ t := by
  simp [Taylm.polyOf]

theorem Taylm.polyOf_ofFn {h : ℕ} (F : Fin h → ℝ × (Fin n → ℕ)) (t : Vec ℝ n) :
    Taylm.polyOf (List.ofFn F) t = ∑ j, (F j).1 * Taylm.monomial (F j).2 t := by
  simp [Taylm.polyOf, List.sum_ofFn]

-- the monomial is a product, so it splits over a sum of exponents
theorem Taylm.monomial_zero (t : Vec ℝ n) : Taylm.monomial 0 t = 1 := by
  simp [Taylm.monomial]

theorem Taylm.monomial_add (e₁ e₂ : Fin n → ℕ) (t : Vec ℝ n) :
    Taylm.monomial (e₁ + e₂) t = Taylm.monomial e₁ t * Taylm.monomial e₂ t := by
  simp [Taylm.monomial, pow_add, Finset.prod_mul_distrib]

theorem Taylm.monomial_single (j : Fin n) (t : Vec ℝ n) :
    Taylm.monomial (Pi.single j 1) t = t j := by
  rw [Taylm.monomial, Finset.prod_eq_single j]
  · simp
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- On the box every monomial is in `[-1, 1]`, which is what a rounded coefficient pays. -/
theorem Taylm.abs_monomial_le_one {t : Vec ℝ n} (ht : t ∈ Taylm.box n) (e : Fin n → ℕ) :
    |Taylm.monomial e t| ≤ 1 := by
  rw [Taylm.monomial, Finset.abs_prod]
  exact Finset.prod_le_one (fun k _ => abs_nonneg _) fun k _ => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (ht k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
