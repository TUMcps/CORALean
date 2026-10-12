import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Tactic.Abel

/-!
# The error of restarted Krylov steps as a sum of propagated local errors

[1, Eq. 7.2]: with `v^{[j]} = E(Δt_j)v^{[j-1]}`, `w^{[j]} = S^{[j]}_m(Δt_j)w^{[j-1]}`,
`w^{[0]} = v`, the accumulated error is
`L⋆_m(t)v = v^{[N]} - w^{[N]} = Σ_{j=1}^N E(Δt_N)⋯E(Δt_{j+1})L^{[j]}_m(Δt_j)w^{[j-1]}`, by
induction from `v^{[j]} - w^{[j]} = E(Δt_j)(v^{[j-1]} - w^{[j-1]}) + L^{[j]}_m(Δt_j)w^{[j-1]}`.
The steps are taken from `0` here, `P a N = E_{N-1} ∘ ⋯ ∘ E_a` (the identity for `a ≥ N`), for
any additive maps `E_j` and any maps `S_j` on an additive group.

## References

* [1] T. Jawecki, W. Auzinger, O. Koch. "Computable upper error bounds for Krylov approximations
  to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 60(1):157-197,
  2020.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type*} [AddCommGroup X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 7.2]: `v^{[N]} - w^{[N]} = Σ_{j<N} E_{N-1}⋯E_{j+1}(E_j w^{[j]} - S_j w^{[j]})` for
`v^{[j+1]} = E_j v^{[j]}`, `w^{[j+1]} = S_j w^{[j]}`, `v^{[0]} = w^{[0]}`. -/
theorem Krylov.restarted_error_eq_sum (E : ℕ → X →+ X) (S : ℕ → X → X) (v w : ℕ → X)
    (hv : ∀ j, v (j + 1) = E j (v j)) (hw : ∀ j, w (j + 1) = S j (w j)) (h0 : v 0 = w 0) :
    let P : ℕ → ℕ → (X →+ X) := fun a N =>
      Nat.rec (AddMonoidHom.id X)
        (fun k acc => if a ≤ k then (E k).comp acc else AddMonoidHom.id X) N
    ∀ N, v N - w N
      = ∑ j ∈ Finset.range N, P (j + 1) N (E j (w j) - S j (w j)) := by -- --- PROOF ---
  intro P N
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    -- one step: `v^{[N+1]} - w^{[N+1]} = E_N(v^{[N]} - w^{[N]}) + (E_N - S_N)w^{[N]}`
    have hsplit : v (N + 1) - w (N + 1) = E N (v N - w N) + (E N (w N) - S N (w N)) := by
      rw [hv, hw, map_sub]
      abel
    -- `P (j+1) (N+1) = E_N ∘ P (j+1) N` for `j < N`, and `P (N+1) (N+1)` is the identity
    have hP : ∀ j ∈ Finset.range N, P (j + 1) (N + 1) = (E N).comp (P (j + 1) N) := by
      intro j hj
      have : j + 1 ≤ N := Finset.mem_range.1 hj
      simp only [P, if_pos this]
    have hPN : P (N + 1) (N + 1) = AddMonoidHom.id X := by
      simp only [P, if_neg (Nat.not_succ_le_self N)]
    rw [hsplit, ih, Finset.sum_range_succ, hPN, map_sum, AddMonoidHom.id_apply]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by rw [hP j hj, AddMonoidHom.comp_apply]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
