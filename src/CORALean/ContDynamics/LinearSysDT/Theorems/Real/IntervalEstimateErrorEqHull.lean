module

public import CORALean.ContDynamics.LinearSysDT.Operations.IntervalEstimate
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachErrorSet
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.IntervalAttained
public import CORALean.ContSet.Interval.Real.Definitions.Hull
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-!
# The error box of the reachability-based estimator is the hull of the reachable error

Eq. 26 of [1, Thm. 2]: `[e̲_k, e̅_k] = Box(Ω_k)`. The box [1, Alg. 1] forms in line 5,
`Box(S_x) ⊕ S_w ⊕ S_v`, contains the reachable error set `Ω_k` (its Eq. 24) and is its interval
hull. After `k` steps `S_x = (A - LC)ᵏ ⟨0, H₀⟩`, `S_w = ⨁_{i<k} Box((A - LC)ⁱ E W)` and `S_v`
alike, which is its Eq. 21; each box is attained by a point of its zonotope
(`Zonotope.interval_attained`), so in each coordinate their sum is attained by a point of `Ω_k`
(its Eq. 25, [1, Property 2]).

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Real

variable {n nu ny nw nv : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- the four set variables of the state after `k` steps, in closed form
theorem LinearSysDT.aux_intervalEstimateState_closed (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (X₀ : Zonotope (Vec ℝ n)) (W : Zonotope (Vec ℝ sys.r)) (V : Zonotope (Vec ℝ sys.s))
    (u : ℕ → Vec ℝ sys.m) (y : ℕ → Vec ℝ sys.q) (k : ℕ) :
    let s := LinearSysDT.intervalEstimateState sys L X₀ W V u y
    (s k).Sx.construct = (((sys.A - L * sys.C) ^ k) *ᵥ ·) ''
        (⟨X₀.h, 0, X₀.G⟩ : Zonotope (Vec ℝ n)).construct ∧
      (s k).Dw.construct = (((sys.A - L * sys.C) ^ k * sys.E) *ᵥ ·) '' W.construct ∧
      (s k).Dv.construct = (((sys.A - L * sys.C) ^ k * -(L * sys.F)) *ᵥ ·) '' V.construct ∧
      (s k).Sw.sup = ∑ i ∈ Finset.range k, (s i).Dw.interval.sup ∧
      (s k).Sw.inf = ∑ i ∈ Finset.range k, (s i).Dw.interval.inf ∧
      (s k).Sv.sup = ∑ i ∈ Finset.range k, (s i).Dv.interval.sup ∧
      (s k).Sv.inf = ∑ i ∈ Finset.range k, (s i).Dv.interval.inf := by -- --- PROOF ---
  intro s
  induction k with
  | zero =>
    refine ⟨by simp [s, LinearSysDT.intervalEstimateState], ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simpa [s, LinearSysDT.intervalEstimateState] using (Zonotope.mtimes_exact sys.E W).symm
    · simpa [s, LinearSysDT.intervalEstimateState] using
        (Zonotope.mtimes_exact (-(L * sys.F)) V).symm
  | succ k ih =>
    obtain ⟨hx, hw, hv, hws, hwi, hvs, hvi⟩ := ih
    -- one more step maps each set through `A - L C` and adds one box to `S_w`, `S_v`
    have hstep : s (k + 1) = LinearSysDT.intervalEstimateStep sys L (u k) (y k) (s k) := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hstep, LinearSysDT.intervalEstimateStep, Finset.sum_range_succ]
    · rw [← Zonotope.mtimes_exact, hx, Set.image_image]
      simp [mulVec_mulVec, pow_succ']
    · rw [← Zonotope.mtimes_exact, hw, Set.image_image]
      simp [mulVec_mulVec, pow_succ', Matrix.mul_assoc]
    · rw [← Zonotope.mtimes_exact, hv, Set.image_image]
      simp [mulVec_mulVec, pow_succ', Matrix.mul_assoc]
    · exact congrArg (· + _) hws
    · exact congrArg (· + _) hwi
    · exact congrArg (· + _) hvs
    · exact congrArg (· + _) hvi


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.intervalEstimate_error_eq_hull (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (X₀ : Zonotope (Vec ℝ n)) (W : Zonotope (Vec ℝ sys.r)) (V : Zonotope (Vec ℝ sys.s))
    (u : ℕ → Vec ℝ sys.m) (y : ℕ → Vec ℝ sys.q) (k : ℕ) :
    let s := LinearSysDT.intervalEstimateState sys L X₀ W V u y k
    LinearSysDT.reachErrorSet sys L X₀ W V k ⊆
        (s.Sx.interval.plus (s.Sw.plus s.Sv)).construct ∧
      s.Sx.interval.plus (s.Sw.plus s.Sv) =
        Interval.hull (LinearSysDT.reachErrorSet sys L X₀ W V k) := by -- --- PROOF ---
  intro s
  set S := LinearSysDT.intervalEstimateState sys L X₀ W V u y
  set Ω := LinearSysDT.reachErrorSet sys L X₀ W V k
  have hcl := fun i => LinearSysDT.aux_intervalEstimateState_closed sys L X₀ W V u y i
  obtain ⟨hx, -, -, hws, hwi, hvs, hvi⟩ := hcl k
  -- the box's bounds, coordinate by coordinate
  have hsup : ∀ j, (s.Sx.interval.plus (s.Sw.plus s.Sv)).sup j = s.Sx.interval.sup j +
      ∑ i ∈ Finset.range k, (S i).Dw.interval.sup j +
        ∑ i ∈ Finset.range k, (S i).Dv.interval.sup j := fun j => by
    show s.Sx.interval.sup j + (s.Sw.sup j + s.Sv.sup j) = _
    rw [hws, hvs, Finset.sum_apply, Finset.sum_apply, add_assoc]
  have hinf : ∀ j, (s.Sx.interval.plus (s.Sw.plus s.Sv)).inf j = s.Sx.interval.inf j +
      ∑ i ∈ Finset.range k, (S i).Dw.interval.inf j +
        ∑ i ∈ Finset.range k, (S i).Dv.interval.inf j := fun j => by
    show s.Sx.interval.inf j + (s.Sw.inf j + s.Sv.inf j) = _
    rw [hwi, hvi, Finset.sum_apply, Finset.sum_apply, add_assoc]
  -- every point of `Ω_k` lies in the box
  have hsub : Ω ⊆ (s.Sx.interval.plus (s.Sw.plus s.Sv)).construct := by
    rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ j
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetSum _ _ _).mp hb
    obtain ⟨g', hg', rfl⟩ := (Set.mem_finsetSum _ _ _).mp hc
    have ha' : a ∈ s.Sx.construct := by rw [hx]; exact ha
    have hgi : ∀ i ∈ Finset.range k, g i ∈ (S i).Dw.construct := fun i hi => by
      rw [(hcl i).2.1]; exact hg hi
    have hgi' : ∀ i ∈ Finset.range k, g' i ∈ (S i).Dv.construct := fun i hi => by
      rw [(hcl i).2.2.1]; exact hg' hi
    -- each summand within its own zonotope's box
    have hA : s.Sx.interval.inf j ≤ a j ∧ a j ≤ s.Sx.interval.sup j :=
      Zonotope.interval_contains _ ha' j
    have hB : ∀ i ∈ Finset.range k, (S i).Dw.interval.inf j ≤ g i j ∧
        g i j ≤ (S i).Dw.interval.sup j := fun i hi => Zonotope.interval_contains _ (hgi i hi) j
    have hC : ∀ i ∈ Finset.range k, (S i).Dv.interval.inf j ≤ g' i j ∧
        g' i j ≤ (S i).Dv.interval.sup j := fun i hi =>
      Zonotope.interval_contains _ (hgi' i hi) j
    change (s.Sx.interval.plus (s.Sw.plus s.Sv)).inf j ≤
        (a + ∑ i ∈ Finset.range k, g i + ∑ i ∈ Finset.range k, g' i) j ∧
      (a + ∑ i ∈ Finset.range k, g i + ∑ i ∈ Finset.range k, g' i) j ≤
        (s.Sx.interval.plus (s.Sw.plus s.Sv)).sup j
    rw [hsup, hinf]
    simp only [Pi.add_apply, Finset.sum_apply]
    constructor
    · linarith [hA.1, Finset.sum_le_sum fun i hi => (hB i hi).1,
        Finset.sum_le_sum fun i hi => (hC i hi).1]
    · linarith [hA.2, Finset.sum_le_sum fun i hi => (hB i hi).2,
        Finset.sum_le_sum fun i hi => (hC i hi).2]
  refine ⟨hsub, ?_⟩
  -- each bound is attained by a point of `Ω_k`, summed from attaining points
  have hatt : ∀ j, (∃ e ∈ Ω, e j = (s.Sx.interval.plus (s.Sw.plus s.Sv)).sup j) ∧
      ∃ e ∈ Ω, e j = (s.Sx.interval.plus (s.Sw.plus s.Sv)).inf j := fun j => by
    obtain ⟨⟨a, ha, haj⟩, ⟨a', ha', haj'⟩⟩ := s.Sx.interval_attained j
    have hDw : ∀ i, (∃ z ∈ (S i).Dw.construct, z j = (S i).Dw.interval.sup j) ∧
        ∃ z ∈ (S i).Dw.construct, z j = (S i).Dw.interval.inf j := fun i =>
      (S i).Dw.interval_attained j
    have hDv : ∀ i, (∃ z ∈ (S i).Dv.construct, z j = (S i).Dv.interval.sup j) ∧
        ∃ z ∈ (S i).Dv.construct, z j = (S i).Dv.interval.inf j := fun i =>
      (S i).Dv.interval_attained j
    -- one attaining point per summand and per side
    choose g hg hgj using fun i => (hDw i).1
    choose g' hg' hgj' using fun i => (hDw i).2
    choose f hf hfj using fun i => (hDv i).1
    choose f' hf' hfj' using fun i => (hDv i).2
    rw [hx] at ha ha'
    have hmem : ∀ a ∈ (((sys.A - L * sys.C) ^ k) *ᵥ ·) ''
        (⟨X₀.h, 0, X₀.G⟩ : Zonotope (Vec ℝ n)).construct, ∀ g f : ℕ → Vec ℝ n,
        (∀ i, g i ∈ (S i).Dw.construct) → (∀ i, f i ∈ (S i).Dv.construct) →
        a + ∑ i ∈ Finset.range k, g i + ∑ i ∈ Finset.range k, f i ∈ Ω := by
      intro a ha g f hg hf
      refine Set.add_mem_add (Set.add_mem_add ha ?_) ?_
      · exact Set.finsetSum_mem_finsetSum _ _ _ fun i _ => by rw [← (hcl i).2.1]; exact hg i
      · exact Set.finsetSum_mem_finsetSum _ _ _ fun i _ => by rw [← (hcl i).2.2.1]; exact hf i
    refine ⟨⟨_, hmem a ha g f hg hf, ?_⟩, ⟨_, hmem a' ha' g' f' hg' hf', ?_⟩⟩
    · rw [hsup]; simp only [Pi.add_apply, Finset.sum_apply, haj, hgj, hfj]
    · rw [hinf]; simp only [Pi.add_apply, Finset.sum_apply, haj', hgj', hfj']
  -- so the box's bounds are the least and greatest coordinates over `Ω_k`
  have hinf' : (s.Sx.interval.plus (s.Sw.plus s.Sv)).inf = (Interval.hull Ω).inf :=
    funext fun j => by
      obtain ⟨e, he, hej⟩ := (hatt j).2
      show _ = sInf ((fun x : Vec ℝ n => x j) '' Ω)
      refine (IsLeast.csInf_eq (s := (fun x : Vec ℝ n => x j) '' Ω) ⟨⟨e, he, hej⟩, ?_⟩).symm
      rintro _ ⟨x, hx', rfl⟩
      exact (hsub hx' j).1
  have hsup' : (s.Sx.interval.plus (s.Sw.plus s.Sv)).sup = (Interval.hull Ω).sup :=
    funext fun j => by
      obtain ⟨e, he, hej⟩ := (hatt j).1
      show _ = sSup ((fun x : Vec ℝ n => x j) '' Ω)
      refine (IsGreatest.csSup_eq (s := (fun x : Vec ℝ n => x j) '' Ω) ⟨⟨e, he, hej⟩, ?_⟩).symm
      rintro _ ⟨x, hx', rfl⟩
      exact (hsub hx' j).2
  calc s.Sx.interval.plus (s.Sw.plus s.Sv) =
        ⟨(s.Sx.interval.plus (s.Sw.plus s.Sv)).inf,
          (s.Sx.interval.plus (s.Sw.plus s.Sv)).sup⟩ := rfl
    _ = Interval.hull Ω := by rw [hinf', hsup']

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
