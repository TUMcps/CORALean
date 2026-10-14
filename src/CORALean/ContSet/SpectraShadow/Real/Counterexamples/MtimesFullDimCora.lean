module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

/-!
# `SpectraShadow.mtimesFullDimCora`: the `fullDim` flag of `M * SpS` as CORA's code sets it

`@spectraShadow/mtimes.m` (l. 53-67) deduces the cached properties of `M * SpS`:

```
if isscalar(M) || rank(full(M)) == dim(SpS)
    if ~isempty(SpS.bounded.val) && SpS.bounded.val   SpS_out.bounded.val = true;
    if ~isempty(SpS.fullDim.val) && SpS.fullDim.val   SpS_out.fullDim.val = true;
```

The comment says "M full rank". For `M` of size `m x n` the rank equals `dim(SpS) = n` also for a
tall `M` with `m > n` of full column rank, whose image lies in an `n`-dimensional subspace of
`R^m` and is not full-dimensional. The right test is `rank(M) == size(M,1)`. `isFullDim` returns
the cached `fullDim.val` before anything else. The flag is `some b` when set and `none` when empty.
Read from the source, not run.

# CORA's `M * SpS` for a tall `M` is flagged full-dimensional

`SpS = spectraShadow.Inf(1)` (the real line, `fullDim.val = true` set by `Inf.m`) and
`M = [1; 0]` (rank `1 = dim(SpS)`): `M * SpS` is the first axis of `R^2`, with empty interior,
and `isFullDim(M * SpS)` returns `true`. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- The cached `fullDim` flag of `M * SpS` from `isscalar(M)`, `rank(M)`, `dim(SpS)` and the flag
of `SpS` (`none` for unset). -/
def SpectraShadow.mtimesFullDimCora (isScalar : Bool) (rankM dimS : ℕ)
    (fullDim : Option Bool) : Option Bool :=
  -- isscalar(M) || rank(full(M)) == dim(SpS)
  if isScalar = true ∨ rankM = dimS then
    -- ~isempty(SpS.fullDim.val) && SpS.fullDim.val
    if fullDim = some true then some true else none
  else none

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `M = [1; 0]` (not a scalar, rank `1`) on a one-dimensional full-dimensional shadow the
flag is `true`, yet the image `{(x, 0)}` has no interior point in `R^2`. -/
theorem SpectraShadow.mtimesFullDim_cora_counterexample :
    SpectraShadow.mtimesFullDimCora false 1 1 (some true) = some true ∧
      ∀ p : Fin 2 → ℝ, p ∉ interior {q : Fin 2 → ℝ | q 1 = 0} := by -- --- PROOF ---
  refine ⟨by simp [SpectraShadow.mtimesFullDimCora], fun p hp => ?_⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hp
  obtain ⟨ε, hε, hball⟩ := hp
  have h0 : p 1 = 0 := hball (Metric.mem_ball_self hε)
  have h1 : Function.update p 1 (p 1 + ε / 2) ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    by_cases hi : i = 1
    · subst hi
      simp only [Function.update_self, Real.dist_eq]
      rw [show p 1 + ε / 2 - p 1 = ε / 2 by ring, abs_of_pos (by linarith)]
      linarith
    · simp [Function.update_of_ne hi, hε]
  have h2 : p 1 + ε / 2 = 0 := by simpa using hball h1
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
