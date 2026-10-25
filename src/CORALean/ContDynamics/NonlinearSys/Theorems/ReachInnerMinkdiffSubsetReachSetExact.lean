module

public import CORALean.ContDynamics.NonlinearSys.Operations.ReachInnerMinkdiff
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachInnerRtiSubsetReachSetExact

@[expose] public section

/-!
# CORA's `'minkdiff'` inner reachability: every cell is an inner approximation

`reachInnerMinkdiff`, CORA's `nonlinearSys/reachInner` with `'minkdiff'`: every time-point cell
`k` lies in the reachable set `R(k Δt)`, every time-interval cell `k` in `R([k Δt, (k+1) Δt])`
[1, Def. 1], and the cells past the horizon are empty. The induction is over the steps: the
start of step `k` lies in `R(k Δt)`, its `Rtp` in `R((k+1) Δt)`
(`linReachInner_subset_reachSetExact`) and its `Rti` in `R([k Δt, (k+1) Δt])`
(`linReachInner_Rti_subset_reachSetExact`). Each step needs [1, Prop. 1]'s hypotheses
(`IsLinReachInnerCert`), certified by `IsLinReachInnerCert.of_abstractionError`. Runs are under
the constant input `u₀` (CORA's `params.u`), so under any `U ∋ u₀`.

## Inputs
* `ops` – set operations
* `sys` – system
* `u₀` – constant input
* `U` – input set
* `Δt` – step size
* `steps` – number of steps
* `fuel` – bound per error loop
* `X₀` – initial set
* `timePoint` – time-point cells
* `timeInt` – time-interval cells

## Hypotheses
* `hu₀` – input in input set
* `hΔt` – step size nonnegative
* `hcert` – every step has its certificate
* `h` – reachability returned these cells

## Conclusion
* each cell lies in the reachable set at its time

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Set MeasureTheory

variable {n m : ℕ} {𝓛 : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `reachInner` with `'minkdiff'`: time-point cell `k` lies in `R(k Δt)`, time-interval
cell `k` in `R([k Δt, (k+1) Δt])`, and the cells past `steps` are empty, given `Prop. 1`'s
hypotheses at every step. -/
theorem NonlinearSys.reachInnerMinkdiff_subset_reachSetExact
    (ops : NonlinearSys.LinReachInnerOps n 𝓛) (sys : NonlinearSys n m) (u₀ : Vec ℝ m)
    (U : Set (Vec ℝ m)) (hu₀ : u₀ ∈ U) {Δt : ℝ}
    (hΔt : 0 ≤ Δt) (steps fuel : ℕ) (X₀ : Set (Vec ℝ n))
    (hcert : ∀ (T : ℝ) (X : Set (Vec ℝ n)) (e : Vec ℝ n) (st : NonlinearSys.LinReachInnerState n 𝓛),
      X ⊆ sys.reachSetExact (S := 𝒮) (Icc 0 T) X₀ {u₀} T →
      NonlinearSys.linReachInner ops (fun x => sys.f x u₀) Δt fuel X e = some (some st) →
      NonlinearSys.IsLinReachInnerCert sys u₀ Δt X st)
    {timePoint timeInt : ℕ → Set (Vec ℝ n)}
    (h : NonlinearSys.reachInnerMinkdiff ops (fun x => sys.f x u₀) X₀ Δt steps fuel =
      some (timePoint, timeInt)) : -- --- CONCL ---
    (∀ k : ℕ, timePoint k ⊆
      sys.reachSetExact (S := 𝒮) (Icc 0 (k * Δt)) X₀ U (k * Δt)) ∧
    (∀ k : ℕ, timeInt k ⊆ ⋃ t ∈ Icc (k * Δt) ((k + 1) * Δt),
      sys.reachSetExact (S := 𝒮) (Icc 0 t) X₀ U t) ∧
    (∀ k, steps < k → timePoint k = ∅) ∧ (∀ k, steps ≤ k → timeInt k = ∅) := by -- --- PROOF ---
  set RS : ℝ → Set (Vec ℝ n) := fun t =>
    sys.reachSetExact (S := 𝒮) (Icc 0 t) X₀ {u₀} t with hRS
  set RSI : ℕ → Set (Vec ℝ n) := fun k => ⋃ t ∈ Icc ((k : ℝ) * Δt) ((k + 1) * Δt), RS t
    with hRSI
  -- the induction over the steps, from step `k`
  have step : ∀ (j k : ℕ) (R : Set (Vec ℝ n)) (e : Vec ℝ n) (tp ti tp' ti' : ℕ → Set (Vec ℝ n)),
      R ⊆ RS (k * Δt) → (∀ i : ℕ, tp i ⊆ RS (i * Δt)) → (∀ i, ti i ⊆ RSI i) →
      (∀ i, k < i → tp i = ∅) → (∀ i, k ≤ i → ti i = ∅) →
      NonlinearSys.aux_reachInnerMinkdiffLoop ops (fun x => sys.f x u₀) Δt fuel j k R e tp ti =
        some (tp', ti') →
      (∀ i : ℕ, tp' i ⊆ RS (i * Δt)) ∧ (∀ i, ti' i ⊆ RSI i) ∧
        (∀ i, k + j < i → tp' i = ∅) ∧ (∀ i, k + j ≤ i → ti' i = ∅) := by
    intro j
    induction j with
    | zero =>
      -- no step left: the cells are returned as they are
      intro k R e tp ti tp' ti' _ htp hti htp0 hti0 hl
      simp only [NonlinearSys.aux_reachInnerMinkdiffLoop, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact ⟨htp, hti, fun i hi => htp0 i (by omega), fun i hi => hti0 i (by omega)⟩
    | succ j ih =>
      intro k R e tp ti tp' ti' hR htp hti htp0 hti0 hl
      obtain ⟨r, hr, hl⟩ := Option.bind_eq_some_iff.mp hl
      cases r with
      | none =>
        -- `options.empty`: the loop breaks with the cells as they are
        simp only [Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        exact ⟨htp, hti, fun i hi => htp0 i (by omega), fun i hi => hti0 i (by omega)⟩
      | some st =>
        -- step `k`: `Rtp` at `(k+1)Δt`, `Rti` over `[kΔt, (k+1)Δt]`
        have hk : (0 : ℝ) ≤ k * Δt := by positivity
        have cert := hcert _ R e st hR hr
        have h1 : st.Rtp ⊆ RS (((k + 1 : ℕ) : ℝ) * Δt) := by
          have := (NonlinearSys.linReachInner_subset_reachSetExact ops sys u₀ hΔt fuel _ hr _ rfl
              cert).trans
            (sys.reachSetExact_subset_reachSetExact_add X₀ R u₀ hk hΔt hR)
          rwa [show (k : ℝ) * Δt + Δt = ((k + 1 : ℕ) : ℝ) * Δt by push_cast; ring] at this
        have h2 : st.Rti ⊆ RSI k := by
          have := NonlinearSys.linReachInner_Rti_subset_reachSetExact ops sys u₀ X₀ hk hΔt fuel hR
            hr cert
          rwa [show (k : ℝ) * Δt + Δt = ((k : ℝ) + 1) * Δt by ring] at this
        -- the updated cells satisfy the invariant at `k + 1`
        have := ih (k + 1) st.Rtp st.err (Function.update tp (k + 1) st.Rtp)
          (Function.update ti k st.Rti) tp' ti' h1
          (fun i => by
            rcases eq_or_ne i (k + 1) with rfl | hi
            · rw [Function.update_self]; exact h1
            · rw [Function.update_of_ne hi]; exact htp i)
          (fun i => by
            rcases eq_or_ne i k with rfl | hi
            · rw [Function.update_self]; exact h2
            · rw [Function.update_of_ne hi]; exact hti i)
          (fun i hi => by rw [Function.update_of_ne (by omega)]; exact htp0 i (by omega))
          (fun i hi => by rw [Function.update_of_ne (by omega)]; exact hti0 i (by omega)) hl
        refine ⟨this.1, this.2.1, fun i hi => this.2.2.1 i (by omega),
          fun i hi => this.2.2.2 i (by omega)⟩
  -- `R0` is reached at `0`: on `{0}` the constant is a run
  have base : X₀ ⊆ RS 0 := by
    intro y hy
    refine ⟨fun _ => y, fun _ => u₀, ⟨hy, fun _ _ => rfl, aestronglyMeasurable_const,
      fun _ _ => intervalIntegrable_const, continuousOn_const, fun t ht => ?_, fun _ _ => rfl⟩, rfl⟩
    rw [Icc_self, mem_singleton_iff] at ht
    subst ht
    simp
  have hall := step steps 0 X₀ 0 _ _ timePoint timeInt (by simpa using base)
    (fun i => by
      rcases eq_or_ne i 0 with rfl | hi
      · rw [Function.update_self]; simpa using base
      · rw [Function.update_of_ne hi]; exact empty_subset _)
    (fun _ => empty_subset _)
    (fun i hi => by rw [Function.update_of_ne (by omega)])
    (fun _ _ => rfl) h
  -- runs under `u₀` are runs with inputs in `U`
  have mono : ∀ t, RS t ⊆ sys.reachSetExact (S := 𝒮) (Icc 0 t) X₀ U t := by
    rintro t y ⟨x, u, traj, hx⟩
    refine ⟨x, u, ⟨traj.init, fun s hs => ?_, traj.meas, traj.integrable, traj.cont, traj.flow,
      traj.output⟩, hx⟩
    have hu : u s = u₀ := traj.input s hs
    show u s ∈ U
    rw [hu]
    exact hu₀
  refine ⟨fun k => (hall.1 k).trans (mono _), fun k => (hall.2.1 k).trans
    (biUnion_mono subset_rfl fun t _ => mono t), fun k hk => hall.2.2.1 k (by omega),
    fun k hk => hall.2.2.2 k (by omega)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
