module

public import CORALean.Global.Tensor
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Taylm.Real.Definitions.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Taylor models: the representation

CORA's `taylm` (`contSet/@taylm/taylm.m`), the Taylor model of [1, Def. 2]: a polynomial `p` in `n`
variables and a remainder interval `rem`, read over CORA's normalized domain, the box `[-1, 1]ⁿ`
(`box`): its constructor maps a variable's interval onto `[-1, 1]` (`mid + rad · t`), and every
range bound it computes (`interval`) assumes that box. A term is a coefficient and an exponent
vector; the polynomial is a list of them, unsorted and possibly repeating an exponent. Variables are
positional, `Fin n`, where CORA matches them by name (`priv_rescale_dim`). What it means is
functional: `T.Encloses f` says `f t - p t ∈ [rem.inf, rem.sup]` on the box, which is what CORA's
arithmetic is sound for. `construct` is the range set of an array of models over the same variables.

## References

* [1] [M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.](../../../../../references/2018/althoff-arch-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A Taylor model: a list of terms (coefficient, exponents), a remainder interval, and the order
`maxOrder` that `times` truncates to. -/
structure Taylm (n : ℕ) where
  terms : List (ℝ × (Fin n → ℕ))
  /-- The remainder, read through `inf` and `sup`. -/
  rem : Interval ℝ
  /-- The order `times` truncates to, CORA's `max_order`. -/
  maxOrder : ℕ

/-- The monomial with exponent vector `e` at the point `t`. -/
def Taylm.monomial (e : Fin n → ℕ) (t : Vec ℝ n) : ℝ := ∏ k, t k ^ e k

/-- A term list evaluated, stated over the list so an operation can name the value of a
list it is still assembling. -/
def Taylm.polyOf (L : List (ℝ × (Fin n → ℕ))) (t : Vec ℝ n) : ℝ :=
  (L.map fun a => a.1 * Taylm.monomial a.2 t).sum

/-- The polynomial part of a Taylor model at `t`: the sum of its terms. -/
def Taylm.poly (T : Taylm n) (t : Vec ℝ n) : ℝ := Taylm.polyOf T.terms t

/-- The functional semantics: `f` minus the polynomial stays in the remainder on the box. -/
def Taylm.Encloses (T : Taylm n) (f : Vec ℝ n → ℝ) : Prop :=
  ∀ t ∈ Taylm.box n, T.rem.inf ≤ f t - T.poly t ∧ f t - T.poly t ≤ T.rem.sup

/-- The range set of an array of models sharing their variables. -/
def Taylm.construct {m : ℕ} (T : Fin m → Taylm n) : Set (Vec ℝ m) :=
  {x | ∃ t ∈ Taylm.box n, ∀ i,
    (T i).rem.inf ≤ x i - (T i).poly t ∧ x i - (T i).poly t ≤ (T i).rem.sup}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
