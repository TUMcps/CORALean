module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section

/-!
# The error of restarted Krylov steps with exact steps that grow in a gauge

[1, Sec. 7] with a step that is nonexpansive only up to a factor: `Krylov.restarted_error_le`
needs `‖E_j x‖ ≤ ‖x‖`. Here the exact steps `E_j` satisfy `ν(E_j x) ≤ g_j ν(x)` in any subadditive
gauge `ν`, and the accumulated error obeys the recursion of a bound `β`, `β_{j+1} ≥ g_j β_j +
ε_j`, `ε_j` the local error in `ν`. By induction `v^{[j]} - w^{[j]} = E_j(v^{[j-1]} - w^{[j-1]}) +
(E_j - S_j)w^{[j-1]}`.

## Inputs
* `X` – space of iterates
* `ν` – subadditive gauge
* `E` – exact step maps
* `S` – approximate step maps
* `v` – exact iterates
* `w` – approximate iterates
* `g` – growth factors of the exact steps
* `ε` – local errors
* `β` – bound of the accumulated error
* `N` – number of substeps

## Hypotheses
* `hν` – gauge subadditive
* `hν0` – gauge at zero nonpositive
* `hg` – growth factors nonnegative
* `hE` – exact steps grow the gauge by at most `g_j`
* `hv` – exact iterates follow the exact steps
* `hw` – approximate iterates follow the approximate steps
* `h0` – both start at the same vector
* `hloc` – local errors within `ε_j`
* `hβ0` – bound nonnegative at the start
* `hβ` – bound follows the recursion

## Conclusion
* the accumulated error is at most `β_N`

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `ν(v^{[N]} - w^{[N]}) ≤ β_N` for `v^{[j+1]} = E_j v^{[j]}`, `w^{[j+1]} = S_j w^{[j]}`,
`v^{[0]} = w^{[0]}`, `ν(E_j x) ≤ g_j ν(x)`, `ν(E_j w^{[j]} - S_j w^{[j]}) ≤ ε_j`, `g_j ≥ 0`,
`g_j β_j + ε_j ≤ β_{j+1}` for `j < N`, and `β_0 ≥ 0`. -/
theorem Krylov.restarted_error_le_growth {X : Type*} [AddCommGroup X] (ν : X → ℝ)
    (hν : ∀ x y, ν (x + y) ≤ ν x + ν y) (hν0 : ν 0 ≤ 0) (E : ℕ → X →+ X) (S : ℕ → X → X)
    (v w : ℕ → X) (g ε β : ℕ → ℝ) (N : ℕ) (hg : ∀ j < N, 0 ≤ g j)
    (hE : ∀ j < N, ∀ x, ν (E j x) ≤ g j * ν x)
    (hv : ∀ j < N, v (j + 1) = E j (v j)) (hw : ∀ j < N, w (j + 1) = S j (w j))
    (h0 : v 0 = w 0) (hloc : ∀ j < N, ν (E j (w j) - S j (w j)) ≤ ε j) (hβ0 : 0 ≤ β 0)
    (hβ : ∀ j < N, g j * β j + ε j ≤ β (j + 1)) : -- --- CONCL ---
    ν (v N - w N) ≤ β N := by -- --- PROOF ---
  induction N with
  | zero => simpa [h0] using hν0.trans hβ0
  | succ N ih =>
    have ih := ih (fun j hj => hg j (by omega)) (fun j hj => hE j (by omega))
      (fun j hj => hv j (by omega)) (fun j hj => hw j (by omega))
      (fun j hj => hloc j (by omega)) (fun j hj => hβ j (by omega))
    -- one step: `v^{[N+1]} - w^{[N+1]} = E_N(v^{[N]} - w^{[N]}) + (E_N - S_N)w^{[N]}`
    have hsplit : v (N + 1) - w (N + 1) = E N (v N - w N) + (E N (w N) - S N (w N)) := by
      rw [hv N (by omega), hw N (by omega), map_sub]
      abel
    rw [hsplit]
    calc _ ≤ ν (E N (v N - w N)) + ν (E N (w N) - S N (w N)) := hν _ _
      _ ≤ g N * ν (v N - w N) + ε N :=
        add_le_add (hE N (by omega) _) (hloc N (by omega))
      _ ≤ g N * β N + ε N := by gcongr; exact hg N (by omega)
      _ ≤ _ := hβ N (by omega)


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
