module

public import CORALean.ContDynamics.NonlinearSys.Theorems.GlobalAbstrErrEqLocalAbstrErr
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSmulSubOneLe
public import Mathlib.Analysis.Matrix.Normed
public import CORALean.Global.BoxDiameter
public import Mathlib.Analysis.Normed.Group.Pointwise
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `hstep`, derived from (10) at a single fixed linearization matrix

[1, Lemma 2]'s Appendix B expands (10) with `A(Δtₖ)` written `A`, one fixed matrix, the honest
reading for a step that does not re-linearize. `R (k+1) = e^{AΔt}R(k) ⊕ P(k) ⊞ Rabs(k)` and
`R̂ (k+1) = e^{AΔt}R̂(k) ⊕ P(k)` share `P(k)`, and reassociating it away leaves
`R(k) = R̂(k) + E(k)` for the tracked error `E(k+1) := e^{AΔt}E(k) ⊞ Rabs(k)`, `E(0) = {0}`
(`aux_exists_solverError`). The two `boxDiameter` bounds turn it into `hstep`'s
`(1+LΔt)εₖ+εₖ,loc` with `L := ‖A‖e^{t_end‖A‖}`, valid across all of `Δt ∈ (0, t_end]`.

## Inputs
* `A` – state matrix
* `Δt` – step size
* `tEnd` – final time
* `N` – number of steps
* `R` – runs with error
* `Rhat` – error-free runs
* `Rabs` – abstraction error sets
* `P` – particular-solution sets
* `k` – step index

## Hypotheses
* `hΔt` – step size positive
* `htEnd` – step size within final time
* `hR0` – initial runs agree
* `hB1` – run with error follows recursion
* `hB2` – error-free run follows recursion
* `hRhatNe` – error-free runs nonempty
* `hRhatBdd` – error-free runs bounded
* `hRabsNe` – error sets nonempty
* `hRabsConv` – error sets convex
* `hRabsCpt` – error sets compact
* `hk` – index below step count

## Conclusion
* the global error grows by at most a fixed factor plus the local error

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Two points of a bounded `S` never differ, at any one coordinate, by more
than `S`'s own box diameter there. -/
theorem aux_abs_sub_le_boxDiameter {S : Set (Vec ℝ n)} (hS : Bornology.IsBounded S)
    {x y : Vec ℝ n} (hx : x ∈ S) (hy : y ∈ S) (i : Fin n) : -- --- CONCL ---
    |x i - y i| ≤ boxDiameter S i := by -- --- PROOF ---
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · have h1 : x i ≤ sSup ((fun z : Vec ℝ n => z i) '' S) :=
      le_csSup (bddAbove_eval_image hS i) ⟨x, hx, rfl⟩
    have h2 : sInf ((fun z : Vec ℝ n => z i) '' S) ≤ y i :=
      csInf_le (bddBelow_eval_image hS i) ⟨y, hy, rfl⟩
    rw [boxDiameter]; linarith
  · have h1 : y i ≤ sSup ((fun z : Vec ℝ n => z i) '' S) :=
      le_csSup (bddAbove_eval_image hS i) ⟨y, hy, rfl⟩
    have h2 : sInf ((fun z : Vec ℝ n => z i) '' S) ≤ x i :=
      csInf_le (bddBelow_eval_image hS i) ⟨x, hx, rfl⟩
    rw [boxDiameter]; linarith


section
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Applying `M` scales a box diameter by at most `M`'s own operator norm. -/
theorem aux_boxDiameter_mulVec_image_le {M : Mat ℝ n n} {S : Set (Vec ℝ n)} (hne : S.Nonempty)
    (hS : Bornology.IsBounded S) : -- --- CONCL ---
    ‖boxDiameter ((M *ᵥ ·) '' S)‖ ≤ ‖M‖ * ‖boxDiameter S‖ := by -- --- PROOF ---
  -- bound the widest column-`i` gap between two points of `S`, then sandwich `sSup`/`sInf`
  have hcoord : ∀ i : Fin n, boxDiameter ((M *ᵥ ·) '' S) i ≤ ‖M‖ * ‖boxDiameter S‖ := by
    intro i
    have himg : (fun x : Vec ℝ n => x i) '' ((M *ᵥ ·) '' S)
        = (fun x : Vec ℝ n => (M *ᵥ x) i) '' S := by
      rw [Set.image_image]
    have hkey : ∀ x ∈ S, ∀ y ∈ S, (M *ᵥ x) i - (M *ᵥ y) i ≤ ‖M‖ * ‖boxDiameter S‖ := by
      intro x hx y hy
      -- `x - y` never exceeds `S`'s own diameter, and `M` scales it by at most `‖M‖`
      have hxy : ‖x - y‖ ≤ ‖boxDiameter S‖ := by
        rw [pi_norm_le_iff_of_nonneg (norm_nonneg (boxDiameter S))]
        intro j
        rw [Real.norm_eq_abs]
        exact (aux_abs_sub_le_boxDiameter hS hx hy j).trans
          ((le_abs_self _).trans (norm_le_pi_norm (boxDiameter S) j))
      have hsub : (M *ᵥ x) i - (M *ᵥ y) i = (M *ᵥ (x - y)) i := by
        rw [Matrix.mulVec_sub]; rfl
      calc (M *ᵥ x) i - (M *ᵥ y) i = (M *ᵥ (x - y)) i := hsub
        _ ≤ |(M *ᵥ (x - y)) i| := le_abs_self _
        _ = ‖(M *ᵥ (x - y)) i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖M *ᵥ (x - y)‖ := norm_le_pi_norm _ i
        _ ≤ ‖M‖ * ‖x - y‖ := Matrix.linfty_opNorm_mulVec M (x - y)
        _ ≤ ‖M‖ * ‖boxDiameter S‖ := mul_le_mul_of_nonneg_left hxy (norm_nonneg M)
    -- sandwich `sSup` between `sInf` and the bound `hkey` gives every pair
    have hsup : sSup ((fun x : Vec ℝ n => (M *ᵥ x) i) '' S)
        ≤ sInf ((fun x : Vec ℝ n => (M *ᵥ x) i) '' S) + ‖M‖ * ‖boxDiameter S‖ := by
      refine csSup_le (hne.image (fun x : Vec ℝ n => (M *ᵥ x) i)) ?_
      rintro _ ⟨x, hx, rfl⟩
      have h : (M *ᵥ x) i - ‖M‖ * ‖boxDiameter S‖
          ≤ sInf ((fun y : Vec ℝ n => (M *ᵥ y) i) '' S) := by
        refine le_csInf (hne.image (fun y : Vec ℝ n => (M *ᵥ y) i)) ?_
        rintro _ ⟨y, hy, rfl⟩
        linarith [hkey x hx y hy]
      linarith
    rw [boxDiameter, himg]; linarith
  -- `(M *ᵥ ·) '' S` is bounded, which is what `boxDiameter`'s own `sSup`/`sInf` need
  have hb : Bornology.IsBounded ((M *ᵥ ·) '' S) := by
    obtain ⟨C, hC⟩ := hS.exists_norm_le
    apply Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : Vec ℝ n))
      (r := ‖M‖ * C))
    rintro _ ⟨x, hx, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (Matrix.linfty_opNorm_mulVec M x).trans (mul_le_mul_of_nonneg_left (hC x hx)
      (norm_nonneg M))
  -- and its box diameter is nonnegative, so its norm reads off each coordinate directly
  have hnn : ∀ i : Fin n, 0 ≤ boxDiameter ((M *ᵥ ·) '' S) i := fun i => by
    have h1 : sInf ((fun z : Vec ℝ n => z i) '' ((M *ᵥ ·) '' S))
        ≤ sSup ((fun z : Vec ℝ n => z i) '' ((M *ᵥ ·) '' S)) :=
      csInf_le_csSup ((hne.image (M *ᵥ ·)).image (fun z : Vec ℝ n => z i))
        (bddBelow_eval_image hb i) (bddAbove_eval_image hb i)
    rw [boxDiameter]; linarith
  rw [pi_norm_le_iff_of_nonneg (by positivity : (0:ℝ) ≤ ‖M‖ * ‖boxDiameter S‖)]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn i)]
  exact hcoord i

end


/-- A Minkowski sum's box diameter is at most the sum of its summands' own. -/
theorem aux_boxDiameter_add_le {X Y : Set (Vec ℝ n)} (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hX : Bornology.IsBounded X) (hY : Bornology.IsBounded Y) : -- --- CONCL ---
    ‖boxDiameter (X + Y)‖ ≤ ‖boxDiameter X‖ + ‖boxDiameter Y‖ := by -- --- PROOF ---
  have hne : (X + Y).Nonempty := hXne.add hYne
  -- read `X + Y`'s coordinate `i` as a sum-of-projections image over `X ×ˢ Y`
  have hcoord : ∀ i : Fin n, boxDiameter (X + Y) i ≤ ‖boxDiameter X‖ + ‖boxDiameter Y‖ := by
    intro i
    have himg : (fun z : Vec ℝ n => z i) '' (X + Y)
        = (fun p : Vec ℝ n × Vec ℝ n => p.1 i + p.2 i) '' (X ×ˢ Y) := by
      ext v; constructor
      · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩; exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩; exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    -- each summand's own gap is under its own diameter, and the two gaps add
    have hkey : ∀ a ∈ X, ∀ b ∈ Y, ∀ a' ∈ X, ∀ b' ∈ Y,
        (a i + b i) - (a' i + b' i) ≤ ‖boxDiameter X‖ + ‖boxDiameter Y‖ := by
      intro a ha b hb a' ha' b' hb'
      have h1 : a i - a' i ≤ ‖boxDiameter X‖ :=
        (le_abs_self _).trans ((aux_abs_sub_le_boxDiameter hX ha ha' i).trans
          ((le_abs_self _).trans (norm_le_pi_norm (boxDiameter X) i)))
      have h2 : b i - b' i ≤ ‖boxDiameter Y‖ :=
        (le_abs_self _).trans ((aux_abs_sub_le_boxDiameter hY hb hb' i).trans
          ((le_abs_self _).trans (norm_le_pi_norm (boxDiameter Y) i)))
      linarith
    -- sandwich `sSup` between `sInf` and the bound, exactly as `hkey` allows
    have hprodne : (X ×ˢ Y).Nonempty := hXne.prod hYne
    have hsup : sSup ((fun z : Vec ℝ n => z i) '' (X + Y))
        ≤ sInf ((fun z : Vec ℝ n => z i) '' (X + Y)) + (‖boxDiameter X‖ + ‖boxDiameter Y‖) := by
      rw [himg]
      refine csSup_le (hprodne.image _) ?_
      rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      have h : (a i + b i) - (‖boxDiameter X‖ + ‖boxDiameter Y‖)
          ≤ sInf ((fun p : Vec ℝ n × Vec ℝ n => p.1 i + p.2 i) '' (X ×ˢ Y)) := by
        refine le_csInf (hprodne.image _) ?_
        rintro _ ⟨⟨a', b'⟩, ⟨ha', hb'⟩, rfl⟩
        linarith [hkey a ha b hb a' ha' b' hb']
      linarith
    rw [boxDiameter]; linarith
  -- `X + Y` is bounded, so its box diameter is nonnegative and its norm reads off coordinates
  have hb : Bornology.IsBounded (X + Y) := hX.add hY
  have hnn : ∀ i : Fin n, 0 ≤ boxDiameter (X + Y) i := fun i => by
    have h1 : sInf ((fun z : Vec ℝ n => z i) '' (X + Y))
        ≤ sSup ((fun z : Vec ℝ n => z i) '' (X + Y)) :=
      csInf_le_csSup (hne.image _) (bddBelow_eval_image hb i) (bddAbove_eval_image hb i)
    rw [boxDiameter]; linarith
  rw [pi_norm_le_iff_of_nonneg
    (by positivity : (0:ℝ) ≤ ‖boxDiameter X‖ + ‖boxDiameter Y‖)]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn i)]
  exact hcoord i


/-- `R` stays `R̂`'s own run widened by an explicit, well-behaved error set: (B.1)-(B.2)'s
content once the shared `P k` reassociates away, tracked forward instead of read off `⊖`. -/
theorem aux_exists_solverError {A : Mat ℝ n n} {Δt : ℝ} {N : ℕ}
    {R Rhat Rabs P : ℕ → Set (Vec ℝ n)} (hR0 : R 0 = Rhat 0)
    (hB1 : ∀ k < N, R (k + 1) = (exp (Δt • A)).mulVec '' R k + P k + Rabs k)
    (hB2 : ∀ k < N, Rhat (k + 1) = (exp (Δt • A)).mulVec '' Rhat k + P k)
    (hRabsNe : ∀ k < N, (Rabs k).Nonempty) (hRabsConv : ∀ k < N, Convex ℝ (Rabs k))
    (hRabsCpt : ∀ k < N, IsCompact (Rabs k)) : -- --- CONCL ---
    ∀ k ≤ N, ∃ E : Set (Vec ℝ n), E.Nonempty ∧ Convex ℝ E ∧ IsCompact E ∧
      R k = Rhat k + E := by -- --- PROOF ---
  intro k
  induction k with
  | zero => exact fun _ => ⟨{0}, Set.singleton_nonempty 0, convex_singleton 0,
      isCompact_singleton, by simp [hR0]⟩
  | succ k ih =>
    intro hk
    have hkN : k < N := by omega
    obtain ⟨E, hEne, hEconv, hEcpt, hRk⟩ := ih (by omega)
    set M := exp (Δt • A) with hM
    refine ⟨M.mulVec '' E + Rabs k, hEne.image _ |>.add (hRabsNe k hkN),
      (hEconv.linear_image (Matrix.mulVecLin M)).add (hRabsConv k hkN),
      (hEcpt.image (Matrix.mulVecLin M).continuous_of_finiteDimensional).add (hRabsCpt k hkN),
      ?_⟩
    have himg : M.mulVec '' (Rhat k + E) = M.mulVec '' Rhat k + M.mulVec '' E :=
      Set.image_add (Matrix.mulVecLin M)
    rw [hB1 k hkN, hB2 k hkN, hRk, himg]
    abel


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1]`'s `hstep`, honestly derived rather than assumed: for a *fixed* `A`, one step of a
solver "of the form (10)" grows the global error by at most `1 + LΔt` before adding its own
local error, with `L := ‖A‖e^{t_end‖A‖}` independent of `Δt` and of `N`. -/
theorem globalAbstrErr_succ_le_of_solver {A : Mat ℝ n n} {Δt tEnd : ℝ} (hΔt : 0 < Δt)
    (htEnd : Δt ≤ tEnd) {N : ℕ} {R Rhat Rabs P : ℕ → Set (Vec ℝ n)} (hR0 : R 0 = Rhat 0)
    (hB1 : ∀ k < N, R (k + 1) = (exp (Δt • A)).mulVec '' R k + P k + Rabs k)
    (hB2 : ∀ k < N, Rhat (k + 1) = (exp (Δt • A)).mulVec '' Rhat k + P k)
    (hRhatNe : ∀ k ≤ N, (Rhat k).Nonempty) (hRhatBdd : ∀ k ≤ N, Bornology.IsBounded (Rhat k))
    (hRabsNe : ∀ k < N, (Rabs k).Nonempty) (hRabsConv : ∀ k < N, Convex ℝ (Rabs k))
    (hRabsCpt : ∀ k < N, IsCompact (Rabs k)) {k : ℕ} (hk : k < N) : -- --- CONCL ---
    globalAbstrErr (R (k + 1)) (Rhat (k + 1)) ≤
      (1 + ‖A‖ * Real.exp (tEnd * ‖A‖) * Δt) * globalAbstrErr (R k) (Rhat k)
        + localAbstrErr (Rabs k) := by -- --- PROOF ---
  -- `Rk`'s own error set, carried forward one step: `E' := M.mulVec '' E + Rabs k`
  obtain ⟨E, hEne, hEconv, hEcpt, hRk⟩ :=
    aux_exists_solverError hR0 hB1 hB2 hRabsNe hRabsConv hRabsCpt k hk.le
  set M := exp (Δt • A) with hM
  set E' := M.mulVec '' E + Rabs k with hE'def
  have hE'ne : E'.Nonempty := (hEne.image _).add (hRabsNe k hk)
  have hE'conv : Convex ℝ E' := (hEconv.linear_image (Matrix.mulVecLin M)).add (hRabsConv k hk)
  have hE'cpt : IsCompact E' :=
    (hEcpt.image (Matrix.mulVecLin M).continuous_of_finiteDimensional).add (hRabsCpt k hk)
  -- the successor step really does land on `Rhat (k+1) + E'`, by the same reassociation
  have hRsucc : R (k + 1) = Rhat (k + 1) + E' := by
    have himg : M.mulVec '' (Rhat k + E) = M.mulVec '' Rhat k + M.mulVec '' E :=
      Set.image_add (Matrix.mulVecLin M)
    rw [hB1 k hk, hB2 k hk, hRk, himg, hE'def]; abel
  -- Rådström cancellation, `Def. 4`'s two forms of the local error, at each of `Rk`, `R(k+1)`
  have hstep1 : globalAbstrErr (R (k + 1)) (Rhat (k + 1)) = localAbstrErr E' := by
    rw [hRsucc]
    exact globalAbstrErr_eq_localAbstrErr (hRhatNe (k + 1) hk) (hRhatBdd (k + 1) hk) hE'conv
      hE'cpt.isClosed
  have hstep2 : globalAbstrErr (R k) (Rhat k) = localAbstrErr E := by
    rw [hRk]
    exact globalAbstrErr_eq_localAbstrErr (hRhatNe k hk.le) (hRhatBdd k hk.le) hEconv hEcpt.isClosed
  -- both `globalAbstrErr`s read off `Def. 4`'s local measure at `E` and `E'` in turn
  have hMEcpt : IsCompact (M.mulVec '' E) :=
    hEcpt.image (Matrix.mulVecLin M).continuous_of_finiteDimensional
  have hbd1 : ‖boxDiameter (M.mulVec '' E + Rabs k)‖
      ≤ ‖boxDiameter (M.mulVec '' E)‖ + ‖boxDiameter (Rabs k)‖ :=
    aux_boxDiameter_add_le (hEne.image _) (hRabsNe k hk) hMEcpt.isBounded (hRabsCpt k hk).isBounded
  have hbd2 : ‖boxDiameter (M.mulVec '' E)‖ ≤ ‖M‖ * ‖boxDiameter E‖ :=
    aux_boxDiameter_mulVec_image_le hEne hEcpt.isBounded
  have hbound : localAbstrErr E' ≤ ‖M‖ * localAbstrErr E + localAbstrErr (Rabs k) := by
    rw [hE'def]
    unfold localAbstrErr at *
    linarith
  -- `‖M‖ ≤ 1 + LΔt`: the identity's norm plus the Taylor bound on `e^{AΔt} - 1`
  have hone : ‖(1 : Mat ℝ n n)‖ ≤ 1 := by
    classical
    rcases isEmpty_or_nonempty (Fin n) with h | h
    · rw [Subsingleton.elim (1 : Mat ℝ n n) 0, norm_zero]; norm_num
    · have : NormOneClass (Mat ℝ n n) := Matrix.linfty_opNormOneClass
      rw [norm_one]
  -- `Δt ≤ t_end` lets `Real.exp (Δt‖A‖)` be bounded by the `Δt`-free `Real.exp (t_end‖A‖)`
  have hexp := Real.norm_exp_smul_sub_one_le A hΔt.le
  have hmono : Δt * ‖A‖ ≤ tEnd * ‖A‖ := mul_le_mul_of_nonneg_right htEnd (norm_nonneg A)
  have hexp2 : Real.exp (Δt * ‖A‖) ≤ Real.exp (tEnd * ‖A‖) := Real.exp_le_exp.mpr hmono
  have hexp3 : Δt * ‖A‖ * Real.exp (Δt * ‖A‖) ≤ Δt * ‖A‖ * Real.exp (tEnd * ‖A‖) :=
    mul_le_mul_of_nonneg_left hexp2 (by positivity)
  have hMnorm : ‖M‖ ≤ 1 + ‖A‖ * Real.exp (tEnd * ‖A‖) * Δt := by
    have h1 : M = 1 + (exp (Δt • A) - 1) := by rw [hM]; abel
    calc ‖M‖ ≤ ‖(1 : Mat ℝ n n)‖ + ‖exp (Δt • A) - 1‖ := by rw [h1]; exact norm_add_le _ _
      _ ≤ 1 + Δt * ‖A‖ * Real.exp (tEnd * ‖A‖) := by linarith
      _ = 1 + ‖A‖ * Real.exp (tEnd * ‖A‖) * Δt := by ring
  have hEnn : 0 ≤ localAbstrErr E := norm_nonneg _
  calc globalAbstrErr (R (k + 1)) (Rhat (k + 1)) = localAbstrErr E' := hstep1
    _ ≤ ‖M‖ * localAbstrErr E + localAbstrErr (Rabs k) := hbound
    _ ≤ (1 + ‖A‖ * Real.exp (tEnd * ‖A‖) * Δt) * localAbstrErr E + localAbstrErr (Rabs k) := by
        gcongr
    _ = (1 + ‖A‖ * Real.exp (tEnd * ‖A‖) * Δt) * globalAbstrErr (R k) (Rhat k)
        + localAbstrErr (Rabs k) := by rw [hstep2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
