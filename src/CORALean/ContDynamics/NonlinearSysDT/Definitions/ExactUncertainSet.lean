module

public import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT

@[expose] public section

/-!
# The exact uncertain state set of a measured nonlinear run

[1, Def. 1]: for `x_{k+1} = f(x_k, w_k)`, `y_k = g(x_k, v_k)` with `w_k ∈ W`, `v_k ∈ V`, `x_0 ∈
X_0` and the measured outputs `y_1, …, y_k`, `X_k` is the set of states `x_k` of runs consistent
with the measurements. The paper writes "`(x_j = f(x_{j-1}, w_{j-1}), y_i = g(x_j, v_j))_1^k`" with
a stray index `i` on `y`; it is read as `y_j = g(x_j, v_j)`, `j = 1, …, k`. The disturbances `w_j`
are `w_0, …, w_{k-1}` and the noises `v_1, …, v_k`, as in the paper. `g` is an argument:
`NonlinearSysDT` carries `f`, with `w` as its input.

## References

* [1] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 41(6):1035-1043, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `{x_k | x_0 ∈ X_0, x_{j+1} = f(x_j, w_j), w_j ∈ W, y_j = g(x_j, v_j), v_j ∈ V}`. -/
def NonlinearSysDT.exactUncertainSet {n nw nv p : ℕ} (sys : NonlinearSysDT n nw)
    (g : Vec ℝ n → Vec ℝ nv → Vec ℝ p) (W : Set (Vec ℝ nw)) (V : Set (Vec ℝ nv))
    (X₀ : Set (Vec ℝ n)) (y : ℕ → Vec ℝ p) (k : ℕ) : Set (Vec ℝ n) :=
  {x | ∃ (xs : ℕ → Vec ℝ n) (ws : ℕ → Vec ℝ nw) (vs : ℕ → Vec ℝ nv), xs 0 ∈ X₀ ∧
    (∀ j < k, ws j ∈ W ∧ xs (j + 1) = sys.f (xs j) (ws j)) ∧
    (∀ j, 1 ≤ j → j ≤ k → vs j ∈ V ∧ y j = g (xs j) (vs j)) ∧ xs k = x}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
