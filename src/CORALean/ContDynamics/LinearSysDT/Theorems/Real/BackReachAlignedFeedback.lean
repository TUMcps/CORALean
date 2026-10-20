module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.BackReachAlignedControl

@[expose] public section

/-!
# A feedback that reaches `Z₀` from `Z̲_k` in `k` steps

[1, Sec. IV-B.2]: "for any initial state `x₀ ∈ Z̲_k`, iteratively applying `u_t ∈
U(x_t, Z̲_{k-t-1})` yields a feedback control strategy … into the target set in
precisely `k` steps, regardless of the disturbance inputs." The strategy `π t x` is an
input steering `x` into `Z̲_{k-t-1}` against every disturbance, which
`backReachAligned_control` provides on `Z̲_{k-t}`; by induction `x_t ∈ Z̲_{k-t}`. The
strategy is shown to exist, not computed: computing it is (16)'s linear program.

## Inputs
* `A` – state matrix
* `B` – input matrix
* `E` – disturbance matrix
* `K` – offset
* `U` – input zonotope
* `W` – disturbance set
* `Z₀` – target zonotope
* `σ` – alignment choice per zonotope
* `k` – step

## Hypotheses
* `hA` – state matrix invertible
* `hσ` – alignments inside the scaling range and around the disturbance set

## Conclusion
* a feedback reaches the target in `k` steps against every disturbance

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward
      reachable sets for uncertain linear systems". IEEE Control Systems Letters,
      6:1555-1560, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix

variable {n m p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. IV-B.2]: some feedback keeps the inputs in `U` and puts every closed-loop
run from `Z̲_k` into `Z₀` at step `k`, whatever the disturbances in `W`. -/
theorem LinearSysDT.backReachAligned_feedback {A : Mat ℝ n n} (hA : IsUnit A.det)
    (B : Mat ℝ n m) (E : Mat ℝ n p) (K : Vec ℝ n) (U : Zonotope (Vec ℝ m)) (W : Set (Vec ℝ p))
    (Z₀ : Zonotope (Vec ℝ n)) (σ : (Z : Zonotope (Vec ℝ n)) → Vec ℝ n × (Fin Z.h → ℝ))
    (hσ : ∀ Z, (∀ i, 0 ≤ (σ Z).2 i ∧ (σ Z).2 i ≤ 1) ∧
      (E *ᵥ ·) '' W ⊆ (Z.aligned (σ Z).1 (σ Z).2).construct) (k : ℕ) : -- --- CONCL ---
    ∃ π : ℕ → Vec ℝ n → Vec ℝ m, ∀ (x : ℕ → Vec ℝ n) (w : ℕ → Vec ℝ p),
      x 0 ∈ (Zonotope.backReachAligned A B K U Z₀ σ k).construct → (∀ t, w t ∈ W) →
      (∀ t < k, x (t + 1) = A *ᵥ x t + B *ᵥ π t (x t) + E *ᵥ w t + K) →
      x k ∈ Z₀.construct ∧ ∀ t < k, π t (x t) ∈ U.construct := by -- --- PROOF ---
  let Z := Zonotope.backReachAligned A B K U Z₀ σ
  -- an input steering `y` into `Z_{k-t-1}` against all of `W`, where one exists
  let good : ℕ → Vec ℝ n → Vec ℝ m → Prop := fun t y u =>
    u ∈ U.construct ∧ ∀ v ∈ W, A *ᵥ y + B *ᵥ u + E *ᵥ v + K ∈ (Z (k - (t + 1))).construct
  have hstep : ∀ t < k, ∀ y ∈ (Z (k - t)).construct, ∃ u, good t y u := by
    intro t ht y hy
    rw [show k - t = k - (t + 1) + 1 by omega] at hy
    obtain ⟨⟨u, hu, hdu⟩, hall⟩ :=
      LinearSysDT.backReachAligned_control hA B E K U W Z₀ σ hσ (k - (t + 1)) y hy
    exact ⟨u, hu, hall u hdu⟩
  classical
  refine ⟨fun t y => if h : ∃ u, good t y u then h.choose else 0, fun x w hx0 hw hx => ?_⟩
  -- every state of the run up to `k` is in `Z_{k-t}`, and every input it takes is good
  have hrun : ∀ t ≤ k, x t ∈ (Z (k - t)).construct := by
    intro t
    induction t with
    | zero => intro _; simpa using hx0
    | succ t ih =>
      intro ht
      have hex := hstep t (by omega) (x t) (ih (by omega))
      have hg := (dif_pos hex : (if h : ∃ u, good t (x t) u then h.choose else 0) = _) ▸
        hex.choose_spec
      rw [hx t (by omega)]
      exact hg.2 (w t) (hw t)
  refine ⟨by simpa [Z, Zonotope.backReachAligned] using hrun k le_rfl, fun t ht => ?_⟩
  have hex := hstep t ht (x t) (hrun t ht.le)
  simp only [dif_pos hex]
  exact hex.choose_spec.1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
