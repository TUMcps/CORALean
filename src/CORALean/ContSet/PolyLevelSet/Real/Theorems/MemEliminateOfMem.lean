module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.Eliminate
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `PolyLevelSet.eliminate` keeps every point

Where the eliminated row is an equation that holds, the surviving rows take their old values: a
surviving row is the old one less `A(j,t) / A(r,t)` times row `r`'s polynomial part with its
monomial `t` split off, which is `b(r) - A(r,t) μ_t` by row `r` itself, and the right-hand side is
shifted by exactly the constant that leaves ([1, Prop. 13], eqs. (35) and (36)).

## Inputs
* `P` – polynomial level set
* `r` – row eliminated
* `t` – monomial solved for
* `x` – point

## Hypotheses
* `hr` – row `r` is an equation
* `hA` – coefficient of `t` in row `r` nonzero
* `hx` – `x` lies in `P`

## Conclusion
* `x` lies in the eliminated level set

## References

* [1] [N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.](../../../../../../references/2023/kochdumper-constrained-polyzonotopes.md)
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point meeting the equation `r` and every other row meets the eliminated system. -/
theorem PolyLevelSet.mem_eliminate_of_mem (P : PolyLevelSet n) (r : Fin P.m) (t : Fin P.q)
    (hr : P.op r = .eq) (hA : P.A r t ≠ 0) {x : Vec ℝ n} (hx : x ∈ P.construct) : -- --- CONCL ---
    x ∈ (P.eliminate r t).construct := by -- --- PROOF ---
  set μ := PolyZonotope.monomial P.R x with hμ
  have hrow : ∑ i, P.A r i * μ i = P.b r := by
    have h := hx.2 r
    rw [hr] at h
    exact sub_eq_zero.mp h
  -- eq. (35), read as what the surviving monomials of row `r` sum to
  have hrest : ∑ i : Fin (P.q - 1), P.A r (dropIdx t i) * μ (dropIdx t i)
      = P.b r - P.A r t * μ t := by
    rw [← hrow, sum_dropIdx t (fun i => P.A r i * μ i)]
    ring
  refine ⟨hx.1, fun j => ?_⟩
  -- eq. (36): a surviving row is the old one, its right-hand side shifted with it
  have hJ : ∑ i : Fin (P.q - 1), P.A (dropIdx r j) (dropIdx t i) * μ (dropIdx t i)
      = (P.A *ᵥ μ) (dropIdx r j) - P.A (dropIdx r j) t * μ t := by
    have hmv : (P.A *ᵥ μ) (dropIdx r j) = ∑ i, P.A (dropIdx r j) i * μ i := rfl
    rw [hmv, sum_dropIdx t (fun i => P.A (dropIdx r j) i * μ i)]
    ring
  -- the corrected row at the old monomials, its rank-one term summed through row `r`
  have hval : ((P.eliminate r t).A *ᵥ PolyZonotope.monomial (P.eliminate r t).R x) j
      = (P.A *ᵥ μ) (dropIdx r j) - P.b r * P.A (dropIdx r j) t / P.A r t := by
    show ∑ i : Fin (P.q - 1), (P.A (dropIdx r j) (dropIdx t i)
        - P.A r (dropIdx t i) * P.A (dropIdx r j) t / P.A r t) * μ (dropIdx t i) = _
    -- each term splits into the old one and its share of row `r`
    have hterm : ∀ i : Fin (P.q - 1),
        (P.A (dropIdx r j) (dropIdx t i) - P.A r (dropIdx t i) * P.A (dropIdx r j) t / P.A r t)
            * μ (dropIdx t i)
          = P.A (dropIdx r j) (dropIdx t i) * μ (dropIdx t i)
            - P.A (dropIdx r j) t / P.A r t * (P.A r (dropIdx t i) * μ (dropIdx t i)) :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib, ← Finset.mul_sum, hJ,
      hrest]
    field_simp
    ring
  -- the right-hand side shifts by the same constant, so the row's value is the old one
  have heval : (P.eliminate r t).eval x j = P.eval x (dropIdx r j) := by
    show ((P.eliminate r t).A *ᵥ PolyZonotope.monomial (P.eliminate r t).R x) j
        - (P.b (dropIdx r j) - P.b r * P.A (dropIdx r j) t / P.A r t)
      = (P.A *ᵥ μ) (dropIdx r j) - P.b (dropIdx r j)
    rw [hval]
    ring
  show (P.op (dropIdx r j)).holds _
  rw [heval]
  exact hx.2 (dropIdx r j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
