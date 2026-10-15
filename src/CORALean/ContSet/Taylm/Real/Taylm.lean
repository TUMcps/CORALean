module

public import CORALean.Global.Tensor
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Taylor models: the representation

CORA's `taylm` (`contSet/@taylm/taylm.m`): a polynomial `p` in `n` variables and a
remainder interval `rem`, read over CORA's normalized domain, the box
`[-1, 1]ⁿ` (`box`). CORA stores no domain: its constructor maps a variable's interval
onto `[-1, 1]` (`mid + rad · t`), and every range bound it computes (`interval`) assumes
that box. So does this one.

A term is a coefficient and an exponent vector; the polynomial is a list of them, unsorted
and possibly repeating an exponent. Identity of variables is positional, `Fin n`, where CORA
matches them by name (`priv_rescale_dim`).

What it means is functional: `T.Encloses f` says `f t - p t ∈ [rem.inf, rem.sup]` on the
box. That is what CORA's arithmetic is sound for: `times` and the elementary functions
are statements about the function the model encloses, not about its range set, which loses
the shared variables. `construct` is the range set of an array of models over the same
variables, CORA's `[p₁(t) + e₁; …]` with `t ∈ [-1, 1]ⁿ`, for the conversions.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Taylm (n : ℕ) where
  terms : List (ℝ × (Fin n → ℕ))
  /-- The remainder, read through `inf` and `sup`. -/
  rem : Interval ℝ
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
  ∀ t ∈ Taylm.box n, T.rem.inf ≤ f t - T.poly t ∧ f t - T.poly t ≤ T.rem.sup

/-- The range set of an array of models sharing their variables. -/
def Taylm.construct {m : ℕ} (T : Fin m → Taylm n) : Set (Vec ℝ m) :=
  {x | ∃ t ∈ Taylm.box n, ∀ i,
    (T i).rem.inf ≤ x i - (T i).poly t ∧ x i - (T i).poly t ≤ (T i).rem.sup}


-- the monomial is a product, so it splits over a sum of exponents

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
