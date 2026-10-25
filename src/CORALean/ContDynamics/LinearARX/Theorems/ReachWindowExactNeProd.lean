module

public import CORALean.ContDynamics.LinearARX.Theorems.ReachOutExactEqSimulate
public import CORALean.ContDynamics.LinearARX.Definitions.ReachWindowExact
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The reachable windows are not the product of the reachable outputs

[1, Eq. 12]'s (13) defines `Ỹ(k:k₊) = Y(k) × ⋯ × Y(k₊)` and (12) then equates it with the joint
window set. They differ once an input enters two outputs of one window:
`y(k) = ũ(k) + ũ(k-1)`, `p = 2`, `ũ ∈ [-1, 1]`. Then `y(2) = 2` and `y(3) = -2` are each
reachable, but `y(2) = 2` forces `ũ(2) = 1` and so `y(3) ≥ 0`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a window exists whose blocks are reachable outputs but which is not reachable

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". 2023 62nd IEEE Conference
      on Decision and Control (CDC), 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.reachWindowExact_ne_prod : -- --- CONCL ---
    let sys : LinearARX ℝ 1 1 2 := ⟨fun _ => 0, fun j => if j.val ≤ 1 then 1 else 0, 1⟩
    let U : ℕ → Set (Vec ℝ 1) := fun _ => {v | |v 0| ≤ 1}
    ∃ w : Vec ℝ (2 * 1), (∀ a : Fin 2, (fun b => w (finProdFinEquiv (a, b))) ∈
      sys.reachOutExact 0 U (2 + a)) ∧ w ∉ sys.reachWindowExact 0 U 2 := by -- --- PROOF ---
  intro sys U
  -- the recursion of this model, read at one coordinate
  have hstep : ∀ (y : ℕ → Vec ℝ 1) (u : ℕ → Vec ℝ 1) (k : ℕ),
      (∑ i : Fin 2, toRealMat (sys.Abar i) *ᵥ y (k - (i + 1))
        + ∑ j : Fin 3, toRealMat (sys.Bbar j) *ᵥ u (k - j)) 0 = u k 0 + u (k - 1) 0 := by
    intro y u k
    simp [sys, Fin.sum_univ_three]
  have hsim : ∀ (c : ℝ) (k : ℕ), 2 ≤ k → sys.simulate 0 (fun _ _ => c) k 0 = c + c := by
    intro c k hk
    rw [LinearARX.simulate, dif_neg (by omega)]
    exact hstep (sys.simulate 0 fun _ _ => c) (fun _ _ => c) k
  -- each block on its own: all inputs `1`, or all `-1`
  have hA : (fun _ => (2 : ℝ)) ∈ sys.reachOutExact 0 U 2 := by
    rw [LinearARX.reachOutExact_eq_simulate]
    refine ⟨fun _ _ => 1, fun _ => by simp [U], ?_⟩
    funext b
    show sys.simulate 0 (fun _ _ => 1) 2 b = 2
    rw [Subsingleton.elim b 0, hsim 1 2 le_rfl]
    norm_num
  have hB : (fun _ => (-2 : ℝ)) ∈ sys.reachOutExact 0 U 3 := by
    rw [LinearARX.reachOutExact_eq_simulate]
    refine ⟨fun _ _ => -1, fun _ => by simp [U], ?_⟩
    funext b
    show sys.simulate 0 (fun _ _ => -1) 3 b = -2
    rw [Subsingleton.elim b 0, hsim (-1) 3 (by norm_num)]
    norm_num
  -- the window `(2, -2)`, block by block
  refine ⟨fun r => if (finProdFinEquiv.symm r).1 = 0 then 2 else -2, fun a => ?_, ?_⟩
  · have hblock : (fun b => (fun r : Fin (2 * 1) => if (finProdFinEquiv.symm r).1 = 0
        then (2 : ℝ) else -2) (finProdFinEquiv (a, b))) = fun _ => if a = 0 then 2 else -2 := by
      funext b
      simp only [Equiv.symm_apply_apply]
    rw [hblock]
    fin_cases a
    · simpa using hA
    · simpa using hB
  · -- jointly: `y(2) = 2` leaves no room for `y(3) = -2`
    rintro ⟨y, u, -, hu, hy, hw⟩
    have h2 := congrFun hw (finProdFinEquiv (0, 0))
    have h3 := congrFun hw (finProdFinEquiv (1, 0))
    simp only [Equiv.symm_apply_apply, LinearARX.stack] at h2 h3
    have e2 := congrFun (hy 2 le_rfl) 0
    have e3 := congrFun (hy 3 (by norm_num)) 0
    rw [hstep] at e2 e3
    have b1 := abs_le.mp (show |u 1 0| ≤ 1 from hu 1)
    have b2 := abs_le.mp (show |u 2 0| ≤ 1 from hu 2)
    have b3 := abs_le.mp (show |u 3 0| ≤ 1 from hu 3)
    norm_num at h2 h3 e2 e3
    linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
