module

public import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolutionLocal

@[expose] public section

/-!
# A Lipschitz field has a solution for every horizon

[1, Def. 2] asks every flow to be Lipschitz, which gives the solutions the paper uses without
saying so: through every point, on `[0, T]` for every `T`. The window of
`lipschitzSolutionLocal` has the same length at every point, so a solution on `(-h, T)` is
extended to `(-h, T + h/2)` by a local one centred at `T - h/2`, which equals it on the overlap
by uniqueness.

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set
open scoped NNReal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [CompleteSpace E] in
/-- Extending a solution on `(-h, T)` by `h/2` to the right, `h / 2 ≤ T`. -/
theorem aux_extend {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) {h T : ℝ} (hh : 0 < h)
    (hT : h ≤ T) (hloc : ∀ y : E, ∃ α : ℝ → E, α 0 = y ∧ ∀ u ∈ Ioo (-h) h, HasDerivAt α (f (α u)) u)
    {γ : ℝ → E} (hγ : ∀ u ∈ Ioo (-h) T, HasDerivAt γ (f (γ u)) u) :
    ∃ γ' : ℝ → E, (∀ u ≤ 0, γ' u = γ u) ∧
      ∀ u ∈ Ioo (-h) (T + h / 2), HasDerivAt γ' (f (γ' u)) u := by -- --- PROOF ---
  set c : ℝ := T - h / 2 with hc
  have hcpos : 0 < c := by linarith
  obtain ⟨α, hα0, hα⟩ := hloc (γ c)
  -- the local solution, centred at `c`, agrees with `γ` on the overlap by uniqueness
  have hcmem : c ∈ Ioo (-h) T := ⟨by linarith, by linarith⟩
  have hα' : ∀ u ∈ Ioo (c - h) (c + h), HasDerivAt (fun v => α (v - c)) (f (α (u - c))) u :=
    fun u hu => by
      have := (hα (u - c) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_sub_const u c
      simpa using this
  have heq : EqOn γ (fun v => α (v - c)) (Ioo (c - h) T) := by
    refine ODE_solution_unique_of_mem_Ioo (a := c - h) (b := T) (t₀ := c) (v := fun _ => f)
      (s := fun _ => univ) (K := K) (fun _ _ => hf.lipschitzOnWith) ⟨by linarith, by linarith⟩
      (fun u hu => ⟨hγ u ⟨by linarith [hu.1], hu.2⟩, trivial⟩)
      (fun u hu => ⟨hα' u ⟨hu.1, by linarith [hu.2]⟩, trivial⟩) ?_
    simp [hα0]
  -- glue: `γ` before `c`, the local solution from `c` on
  set γ' : ℝ → E := fun u => if u < c then γ u else α (u - c) with hγ'
  refine ⟨γ', fun u hu => ?_, fun u hu => ?_⟩
  · simp [hγ', show u < c by linarith]
  · by_cases hu' : u < c
    · have hval : γ' u = γ u := by simp [hγ', hu']
      rw [hval]
      refine (hγ u ⟨hu.1, by linarith⟩).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hu'] with v hv using by simp [hγ', show v < c from hv]
    · have hnear : γ' =ᶠ[nhds u] fun v => α (v - c) := by
        rcases (not_lt.1 hu').eq_or_lt with hce | hlt
        · rw [← hce]
          filter_upwards [Ioo_mem_nhds (show c - h < c by linarith) hcmem.2] with v hv
          by_cases hvc : v < c
          · simp [hγ', hvc, heq ⟨hv.1, hv.2⟩]
          · simp [hγ', hvc]
        · filter_upwards [Ioi_mem_nhds hlt] with v hv
          simp [hγ', not_lt.2 (Set.mem_Ioi.1 hv).le]
      have hval : γ' u = α (u - c) := by simp [hγ', hu']
      rw [hval]
      exact (hα' u ⟨by linarith [not_lt.1 hu'], by linarith [hu.2]⟩).congr_of_eventuallyEq hnear


-- =======================================  MAIN THEOREM  ======================================= --

/-- A solution of `ẋ = f(x)` from `x₀`, with a two-sided derivative on `[0, T]`, [1, Def. 2]. -/
theorem lipschitzSolution {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (x₀ : E) (T : ℝ) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ u ∈ Icc 0 T, HasDerivAt γ (f (γ u)) u := by -- --- PROOF ---
  set h : ℝ := 1 / (2 * (K : ℝ) + 2) with hh
  have hpos : 0 < h := by positivity
  -- each step lengthens the window by `h / 2`
  have step : ∀ n : ℕ, ∀ y : E, ∃ γ : ℝ → E, γ 0 = y ∧
      ∀ u ∈ Ioo (-h) (h + n * (h / 2)), HasDerivAt γ (f (γ u)) u := by
    intro n
    induction n with
    | zero =>
      -- the base case is one local window
      intro y
      obtain ⟨α, h0, hα⟩ := lipschitzSolutionLocal hf y
      exact ⟨α, h0, fun u hu => hα u ⟨by simpa [hh] using hu.1, by simpa [hh] using hu.2⟩⟩
    | succ n ih =>
      -- the step glues a local window centred inside the solution so far
      intro y
      obtain ⟨γ, hγ0, hγ⟩ := ih y
      obtain ⟨γ', hγ'0, hγ'⟩ := aux_extend hf hpos (T := h + n * (h / 2))
        (by have : (0 : ℝ) ≤ n * (h / 2) := by positivity
            linarith) (fun z => lipschitzSolutionLocal hf z) hγ
      refine ⟨γ', by rw [hγ'0 0 le_rfl, hγ0], fun u hu => hγ' u ⟨hu.1, ?_⟩⟩
      have := hu.2
      push_cast at this
      linarith
  -- enough steps to pass the horizon `T`
  obtain ⟨n, hn⟩ := exists_nat_gt (T / (h / 2))
  obtain ⟨γ, hγ0, hγ⟩ := step n x₀
  refine ⟨γ, hγ0, fun u hu => hγ u ⟨by linarith [hu.1], ?_⟩⟩
  have : T < n * (h / 2) := by rwa [div_lt_iff₀ (by positivity)] at hn
  linarith [hu.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
