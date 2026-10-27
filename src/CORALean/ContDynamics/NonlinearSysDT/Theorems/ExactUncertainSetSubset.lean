module

public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ExactUncertainSetSucc

@[expose] public section

/-!
# One step of the guaranteed state estimation algorithm is an outer approximation

[1, Thm. 1]: the three steps of [1, Alg. 1] give an outer approximation of the exact uncertain
state set: if `X̃_k` bounds `X_k`, `X̄` bounds `f(X̃_k, W)` (Step 1, an inclusion function), `X^e`
bounds `X_{y_{k+1}}` (Step 2) and `X̃_{k+1}` bounds `X̄ ∩ X^e` (Step 3), then `X_{k+1} ⊆ X̃_{k+1}`.
The paper takes a bound of `X_{k-1}` as available, which is the first hypothesis; the proof is its
`X_k = f(X_{k-1}, W) ∩ X_{y_k} ⊆ f(X̃_{k-1}, W) ∩ X^e ⊆ X̃_k` with the first step
`exactUncertainSet_succ`. The steps are hypotheses on the sets: how each bound is computed is [1,
Thm. 5], [1, Property 1] and [1, Property 2].

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
* `Xt` – bound of the previous set
* `Xbar` – bound of the predicted set
* `Xe` – bound of the consistent set
* `Xt'` – bound of the intersection

## Hypotheses
* `hprev` – bound holds for previous set
* `hbar` – bound holds for prediction
* `he` – bound holds for consistent set
* `hint` – bound holds for intersection

## Conclusion
* the next exact set lies in the new bound

## References

* [1] [T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 2005.](../../../../../references/2005/alamo-automatica-guaranteed-estimation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.exactUncertainSet_subset {n nw nv p : ℕ} (sys : NonlinearSysDT n nw)
    (g : Vec ℝ n → Vec ℝ nv → Vec ℝ p) (W : Set (Vec ℝ nw)) (V : Set (Vec ℝ nv))
    (X₀ : Set (Vec ℝ n)) (y : ℕ → Vec ℝ p) (k : ℕ) {Xt Xbar Xe Xt' : Set (Vec ℝ n)}
    (hprev : sys.exactUncertainSet g W V X₀ y k ⊆ Xt)
    (hbar : Set.image2 sys.f Xt W ⊆ Xbar)
    (he : NonlinearSysDT.consistentSet g V (y (k + 1)) ⊆ Xe)
    (hint : Xbar ∩ Xe ⊆ Xt') : -- --- CONCL ---
    sys.exactUncertainSet g W V X₀ y (k + 1) ⊆ Xt' := by -- --- PROOF ---
  -- `X_{k+1} = f(X_k, W) ∩ X_y ⊆ f(X̃_k, W) ∩ X^e ⊆ X̄ ∩ X^e ⊆ X̃_{k+1}`
  rw [NonlinearSysDT.exactUncertainSet_succ]
  rintro x ⟨⟨a, ha, w, hw, rfl⟩, hx⟩
  exact hint ⟨hbar ⟨a, hprev ha, w, hw, rfl⟩, he hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
