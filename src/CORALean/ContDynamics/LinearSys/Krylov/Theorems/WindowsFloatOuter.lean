module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.WindowsFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.SubspaceFloatSound
public import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ToSetPoint

@[expose] public section

/-!
# The Krylov windows enclose the flow of the vector at every time of the horizon

If `Krylov.subspaceFloat` accepts its order (the order test of [1, Prop. B.1], extended to every
matrix), then at `t = iΔt + s`, `s ∈ [0, Δt]`, the solution `e^{tA}c` is `ν V y + e` with `y` in
window `i` of the `k`-dimensional system (`reachFloat_outer`, from `e₁`, which the point zonotope
contains) and `‖e‖₂ ≤ tol` (`subspaceFloat_error_le`, valid on all of `[0, t_f]` and
`iΔt + s ≤ NΔt = tFinal ≤ t_f`).
The windows are those of the small system whose curvature is taken at the start of each window; no
set of the state space is formed.

## Inputs
* `p` – Newton steps per norm
* `q` – squarings of the exponential
* `εb` – breakdown threshold
* `A` – matrix
* `c` – start vector
* `k₀` – first order tried
* `step` – growth of the order per try
* `tf` – horizon of the error bound
* `tol` – tolerance
* `fuel` – number of tries
* `Δt` – time step
* `tFinal` – final time
* `η` – Taylor terms
* `ρ` – zonotope order
* `r` – the Krylov subspace

## Hypotheses
* `hq` – at least one squaring
* `htf` – final time within the horizon of the error bound
* `ht0` – final time nonnegative
* `hr` – `r` is what the search returns
* `hok` – the search accepted its order

## Conclusion
* the flow lies in the lifted window plus a ball of the tolerance

## References

* [1] [M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
      Krylov Subspace". IEEE Transactions on Automatic Control,
      2020.](../../../../../../references/2020/althoff-tac-krylov.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Krylov.windowsFloat_outer (p q : ℕ) (hq : 1 ≤ q) (εb : 𝕋) (A : Mat 𝕋 n n)
    (c : Vec 𝕋 n) (k₀ step : ℕ) (tf tol : 𝕋) (fuel : ℕ) (Δt : 𝕋) (tFinal : ℚ) (η ρ : ℕ)
    (htf : (tFinal : ℝ) ≤ toReal tf) (ht0 : 0 ≤ (tFinal : ℝ))
    {r : Krylov.SubspaceFloat 𝕋 n} (hr : r = Krylov.subspaceFloat p q εb A c k₀ step tf tol fuel)
    (hok : r.ok = true) : -- --- CONCL ---
    ∀ Rti Rtp, (Rti, Rtp) ∈ Krylov.windowsFloat r Δt tFinal η ρ →
      ∃ N : ℕ, (N : ℝ) * toReal Δt = tFinal ∧ Rti.length = N ∧
        ∀ (i : ℕ) (hi : i < Rti.length), ∀ s ∈ Set.Icc (0 : ℝ) (toReal Δt),
          ∃ y ∈ Rti[i].toSet, ∃ e : Vec ℝ n, ‖e‖₂ ≤ toReal tol ∧
            exp (((i : ℝ) * toReal Δt + s) • toRealMat A) *ᵥ (fun j => toReal (c j)) =
              toReal r.ν • ((Matrix.of fun (a : Fin n) (b : Fin r.order) =>
                toReal (r.V b)[a]) *ᵥ y) + e := by -- --- PROOF ---
  intro Rti Rtp hmem
  have h1 := Krylov.subspaceFloat_error_le p q hq εb A c k₀ step tf tol (ht0.trans htf) fuel
  rw [← hr] at h1
  obtain ⟨hk1, herr⟩ := h1 hok
  obtain ⟨order, ok, bound, ν, V, H⟩ := r
  obtain ⟨m, rfl⟩ : ∃ m, order = m + 1 := ⟨order - 1, by simp at hk1; omega⟩
  obtain ⟨N, hN, hlen, hflow⟩ := LinearSys.reachFloat_outer _ Rti Rtp hmem
  have hN' : (N : ℝ) * toReal Δt = tFinal := by simpa using hN
  refine ⟨N, hN', hlen, fun i hi s hs => ?_⟩
  -- the time `iΔt + s` is within the horizon of the error bound
  have hiN : i < N := hlen ▸ hi
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le i) hiN
  have hΔ0 : 0 ≤ toReal Δt := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_neg_of_pos_of_neg hNpos hneg]
  have hi1 : ((i : ℝ) + 1) ≤ N := by exact_mod_cast hiN
  have hτ : (i : ℝ) * toReal Δt + s ∈ Set.Icc (0 : ℝ) (toReal tf) :=
    ⟨add_nonneg (mul_nonneg (Nat.cast_nonneg _) hΔ0) hs.1, by
      nlinarith [mul_le_mul_of_nonneg_right hi1 hΔ0, hs.2]⟩
  -- the start `e₁` is the point zonotope's only point
  have hx₀ : toRealVec (fun j : Fin (m + 1) => if j.val = 0 then (one : 𝕋) else zero) ∈
      (Zonotope.point fun j : Fin (m + 1) => if j.val = 0 then (one : 𝕋) else zero).toSet := by
    rw [Zonotope.toSet_point]; exact Set.mem_singleton _
  have hy := hflow i hi _ hx₀ s hs
  have he1 : toRealVec (fun j : Fin (m + 1) => if j.val = 0 then (one : 𝕋) else zero) =
      (Pi.single 0 1 : Fin (m + 1) → ℝ) := by
    funext j
    by_cases hj : j.val = 0
    · have : j = 0 := Fin.ext (by simpa using hj)
      subst this
      simp [toRealVec, toReal_one]
    · have : j ≠ 0 := fun h => hj (by simp [h])
      simp [toRealVec, hj, toReal_zero, this]
  -- the flow lies in the window and the rest is the error
  rw [he1] at hy
  refine ⟨_, hy, _, ?_, (add_sub_cancel _ _).symm⟩
  exact herr m rfl _ hτ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
