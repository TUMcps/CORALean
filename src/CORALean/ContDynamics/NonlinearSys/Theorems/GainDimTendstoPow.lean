import CORALean.ContDynamics.NonlinearSys.Operations.GainDim

/-!
# The limit of the gain as the time span shrinks

`[1, Thm. 2]`: `φᵢ(h;δ) → δ^{qᵢ+1}` as `h → 0`. The whole content is that
`dᵢ(box(R^∞_abs(t)))` vanishes to order `qᵢ+1` at `t = 0`: write it `t^{qᵢ+1}g(t)`
with `g` continuous and `g(0) ≠ 0`, and the ratio of the two spans is
`δ^{qᵢ+1}·g(δh)/g(h)`, whose second factor goes to `1`.

That factorisation is the hypothesis, and it is what `[1, Lemma 3]` and
`[1, (40)]` supply: grouping `[1, (35)]` by `j = p + q⁽ᵖ⁾ᵢ` gives
`2 Σⱼ t^{j+1} Σ_{p+q⁽ᵖ⁾ᵢ=j} Q⁽ᵖ⁾ᵢ(t)/(p+1)!`, and `qᵢ` is the *least* `j` whose
coefficient survives at `t = 0` — `[1, (40)]` prints a maximum; see the paper
page's finding. `[1]`'s proof then passes to the limit inside that series
without uniform control over `p`, which is the step the hypothesis stands in
for; `[1, Prop. 2]`'s constant-`Q⁽ᵖ⁾ᵢ` case is where it is elementary.

`g 0 ≠ 0` is also the nonvanishing `[1, Def. 5]` defers to its readers, `[1, (19)]`'s
`Ψᵢ > 0`. Only `δ ≥ 0` is used: `[1]`'s `δ ∈ [0,1]` is what makes the limit a
contraction rather than what makes it exist.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, (39)]`: where the error's `i`-th width vanishes to order `qᵢ+1`, the
gain of that dimension tends to `δ^{qᵢ+1}`. -/
theorem gainDim_tendsto_pow (A : ℝ → Mat ℝ n n) (Ψ : ℝ → Set (Vec ℝ n)) (i : Fin n)
    {qi : ℕ} {g : ℝ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hg : ContinuousWithinAt g (Set.Ici 0) 0) (hg0 : g 0 ≠ 0)
    (hexp : ∀ᶠ t in 𝓝[≥] (0:ℝ), boxDiameter (abstrSolInf A Ψ t) i = t ^ (qi + 1) * g t) :
    Tendsto (fun h => gainDim A Ψ h δ i) (𝓝[>] (0:ℝ)) (𝓝 (δ ^ (qi + 1))) := by -- --- PROOF ---
  -- the two spans the ratio compares, both reaching `0` from the right
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0:ℝ)) (𝓝[≥] (0:ℝ)) :=
    tendsto_id.mono_right (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hd : Tendsto (fun h : ℝ => δ * h) (𝓝[>] (0:ℝ)) (𝓝[≥] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Tendsto (fun h : ℝ => δ * h) (𝓝 (0:ℝ)) (𝓝 (δ * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact Set.mem_Ici.mpr (mul_nonneg hδ (le_of_lt hh))
  -- `g` is continuous at `0` along both, and its value there is not zero
  have hgh : Tendsto (fun h : ℝ => g h) (𝓝[>] (0:ℝ)) (𝓝 (g 0)) := hg.tendsto.comp hid
  have hgd : Tendsto (fun h : ℝ => g (δ * h)) (𝓝[>] (0:ℝ)) (𝓝 (g 0)) := hg.tendsto.comp hd
  have hlim : Tendsto (fun h : ℝ => δ ^ (qi + 1) * (g (δ * h) / g h)) (𝓝[>] (0:ℝ))
      (𝓝 (δ ^ (qi + 1))) := by
    have hq := (hgd.div hgh hg0).const_mul (δ ^ (qi + 1))
    simpa [div_self hg0] using hq
  refine hlim.congr' ?_
  -- on the right of `0` both spans meet the expansion, and `h^{qᵢ+1}` cancels
  filter_upwards [hid.eventually hexp, hd.eventually hexp, self_mem_nhdsWithin] with h hh hdh hpos
  have hne : (h : ℝ) ^ (qi + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hpos)
  have hX : (δ * h) ^ (qi + 1) * g (δ * h) = δ ^ (qi + 1) * g (δ * h) * h ^ (qi + 1) := by
    rw [mul_pow]; ring
  rw [gainDim, hh, hdh, hX, ← div_div, mul_div_cancel_right₀ _ hne, mul_div_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
