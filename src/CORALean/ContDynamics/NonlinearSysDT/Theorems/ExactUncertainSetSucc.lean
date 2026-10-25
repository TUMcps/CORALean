module

public import CORALean.ContDynamics.NonlinearSysDT.Definitions.ExactUncertainSet
public import CORALean.ContDynamics.NonlinearSysDT.Definitions.ConsistentSet

@[expose] public section

/-!
# The exact uncertain set is the image of the last one met with the consistent set

The line of the proof of [1, Thm. 1] that reads `X_k = f(X_{k-1}, W) ∩ X_{y_k}`: a run of `k + 1`
steps is one of `k` steps and one more, whose end state `x_{k+1} = f(x_k, w_k)` is consistent with
`y_{k+1} = g(x_{k+1}, v_{k+1})`. The paper does not prove it. A run is extended past `k` by
overwriting its state at `k + 1`, its disturbance at `k` and its noise at `k + 1`.

## Inputs
* `n` – state dimension
* `nw` – disturbance dimension
* `nv` – noise dimension
* `p` – output dimension
* `sys` – system
* `g` – measurement map
* `W` – disturbance set
* `V` – noise set
* `X₀` – initial set
* `y` – measured outputs
* `k` – step

## Hypotheses
* none

## Conclusion
* the next exact set is the image met with the consistent set

## References

* [1] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.exactUncertainSet_succ {n nw nv p : ℕ} (sys : NonlinearSysDT n nw)
    (g : Vec ℝ n → Vec ℝ nv → Vec ℝ p) (W : Set (Vec ℝ nw)) (V : Set (Vec ℝ nv))
    (X₀ : Set (Vec ℝ n)) (y : ℕ → Vec ℝ p) (k : ℕ) : -- --- CONCL ---
    sys.exactUncertainSet g W V X₀ y (k + 1) =
      Set.image2 sys.f (sys.exactUncertainSet g W V X₀ y k) W ∩
        NonlinearSysDT.consistentSet g V (y (k + 1)) := by -- --- PROOF ---
  ext x
  constructor
  · -- the run restricted to `k` steps reaches a state whose image under `f` is `x`
    rintro ⟨xs, ws, vs, h0, hstep, hmeas, rfl⟩
    obtain ⟨hw, hs⟩ := hstep k (Nat.lt_succ_self k)
    obtain ⟨hv, hy⟩ := hmeas (k + 1) (Nat.succ_pos k) le_rfl
    refine ⟨⟨xs k, ⟨xs, ws, vs, h0, fun j hj => hstep j (by omega),
      fun j h1 hj => hmeas j h1 (by omega), rfl⟩, ws k, hw, hs.symm⟩, vs (k + 1), hv, hy⟩
  · -- a run to `a` is extended by one step to `f a w`
    rintro ⟨⟨_, ⟨xs, ws, vs, h0, hstep, hmeas, rfl⟩, w, hw, rfl⟩, v, hv, hy⟩
    refine ⟨fun j => if j = k + 1 then sys.f (xs k) w else xs j,
      fun j => if j = k then w else ws j, fun j => if j = k + 1 then v else vs j,
      by simpa using h0, fun j hj => ?_, fun j h1 hj => ?_, by simp⟩
    · -- the old steps, and the new one at `k`
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hne : j ≠ k := Nat.ne_of_lt hj
        have hne1 : j ≠ k + 1 := by omega
        have hne2 : j + 1 ≠ k + 1 := by omega
        simp only [hne, hne1, hne2, if_false]
        exact hstep j hj
      · simp only [if_true, show j ≠ j + 1 by omega, if_false]
        exact ⟨hw, trivial⟩
    · -- the old measurements, and the new one at `k + 1`
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with hj' | rfl
      · have hne : j ≠ k + 1 := by omega
        simp only [hne, if_false]
        exact hmeas j h1 (by omega)
      · simpa using ⟨hv, hy⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
