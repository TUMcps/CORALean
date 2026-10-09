import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

/-!
# `Zonotope.correctedStepDistributed`

The distributed state-bounding zonotope of [1, Prop. 1], one step of one agent `i` of the
interconnected system `x_i(k+1) = Σ_{j ∈ N_i} A_ij x_j(k) + B_i u_i(k) + w_i(k)`,
`y_i(k) = C_i x_i(k) + v_i(k)` [1, Eq. 4]: from the zonotopes `X_j = ⟨c_j, H_j⟩` of the agent's
neighbours `j ∈ N_i`, its input `u_i`, its own measurement `y_i` and its correction matrix `Λ_i`,
`c_i = (I - Λ_iC_i)(Σ_j A_ij c_j + B_i u_i) + Λ_i y_i` and
`H_i = [(I - Λ_iC_i) cat_j {A_ij H_j}  (I - Λ_iC_i) D_{w_i}  Λ_i D_{v_i}]` Eq. 7 of [1, Prop. 1].

The neighbours are enumerated as `Fin q` in the paper's increasing order, so `X a` is the
zonotope of the `a`-th neighbour, of dimension `m a`, and `A a` is `A_ij` at that neighbour; the
agent's own state is one of them, `N_i` containing `i`. The generator blocks `A_ij H_j` are laid
side by side,
each neighbour's own coefficients: `cat` is a concatenation and not a sum, so the coefficients of
two neighbours are independent. `Λ_i` is any matrix; the enclosure holds for each.

## References

* [1] Y. Wang, T. Alamo, V. Puig and G. Cembrano. "A distributed set-membership approach based on
      zonotopes for interconnected systems". IEEE Conference on Decision and Control (CDC),
      pp. 668-673, 2018.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nu nw ny nv q : ℕ} {m : Fin q → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.correctedStepDistributed (Λ : Mat ℝ n ny) (A : ∀ a, Mat ℝ n (m a))
    (B : Mat ℝ n nu) (Dw : Mat ℝ n nw) (C : Mat ℝ ny n) (Dv : Mat ℝ ny nv) (u : Vec ℝ nu)
    (y : Vec ℝ ny) (X : ∀ a, Zonotope (Vec ℝ (m a))) : Zonotope (Vec ℝ n) :=
  let K : Mat ℝ n n := 1 - Λ * C                                             -- I - Λ_iC_i
  { h := (∑ a, (X a).h) + nw + nv
    c := K *ᵥ (∑ a, A a *ᵥ (X a).c + B *ᵥ u) + Λ *ᵥ y                       -- Eq. 7a
    G := Fin.append (Fin.append
      (fun k => K *ᵥ (A (finSigmaFinEquiv.symm k).1 *ᵥ
        (X (finSigmaFinEquiv.symm k).1).G (finSigmaFinEquiv.symm k).2))   -- (I - Λ_iC_i) cat
      (fun j i => (K * Dw) i j))                                           -- (I - Λ_iC_i) D_{w_i}
      (fun j i => (Λ * Dv) i j) }                                          -- Λ_i D_{v_i}, Eq. 7b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
