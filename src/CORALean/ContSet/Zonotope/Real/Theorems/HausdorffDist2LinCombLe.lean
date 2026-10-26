module

public import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.Shift
public import CORALean.Global.EuclideanGenOpNorm
public import CORALean.Global.EuclideanHausdorffDist
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# [1, Prop. 9]: the error of enclosing a linear combination of zonotopes by `linComb`

Given `H = H(t_k)` and the propagated `H' = e^{AΔt_k}H + P^u(Δt_k)` (a matrix image of `H`
shifted by `c_p`, exact by `Zonotope.mtimes`/`shift`), the exact linear combination is
`S = comb(H,H') = Set.linComb H.construct H'.construct` — [1]'s `Def. 7`, the union of segments
between two *convex* sets being their convex hull. `Zonotope.linComb_outer` already gives
`S ⊆ Ŝ` for `Ŝ := H.linComb H'`; this file is the other direction. [1]'s bound is
`√γ_h ‖G_h^{(-)}‖₂`, `G_h^{(-)} = (e^{AΔt_k} - I_n)G_h`, `‖·‖₂` the *matrix* norm (`genOpNorm₂`).
The witness is elementary, not [1]'s Bauer-maximum-principle argument: the *same* `βSum` on both
endpoints of `S`'s segment cancels every term but `v := βDiff - βExtra • βSum`, `‖v‖₂ ≤ 2√γ_h`.

## Inputs
* `A` – state matrix
* `Δtk` – time step
* `H` – zonotope
* `cp` – shift vector

## Hypotheses
* none

## Conclusion
* the linear-combination error is bounded by the generator operator norm

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A coordinate bounded by `1` in magnitude everywhere has `‖·‖₂` bounded by `√`(its count). -/
private theorem aux_norm₂_le_sqrt_card {h : ℕ} {f : Fin h → ℝ} (hf : ∀ j, |f j| ≤ 1) :
    ‖f‖₂ ≤ Real.sqrt h := by
  have hterm : ∀ j : Fin h, f j ^ 2 ≤ (1:ℝ) := fun j => (sq_le_one_iff_abs_le_one (f j)).mpr (hf j)
  refine (Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hterm j)).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- `Fin.sum_univ_add` at `linComb`'s own generator count, stated through the projection since a
binder's type is not something `simp`/`rw` rewrites — the local copy `LinCombOuter.lean`'s own
`Zonotope.aux_sum_univ_linComb` cannot be reused across files (`aux_` names stay file-local). -/
private theorem aux_sum_univ_linComb2 {α : Type} [AddCommGroup α] [Module ℝ α] {Z₁ Z₂ : Zonotope α}
    (f : Fin (Z₁.h + Z₂.h + 1) → α) :
    ∑ j : Fin (Z₁.linComb Z₂).h, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j, f (Fin.natAdd (Z₁.h + Z₂.h) j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 9]: `linComb`'s error against the exact linear combination of `H = H(t_k)` and the
propagated `H(t_{k+1}) = e^{AΔt_k}H + c_p`, at `‖·‖₂`. -/
theorem Zonotope.hausdorffDist₂_linComb_le (A : Mat ℝ n n) (Δtk : ℝ) (H : Zonotope (Vec ℝ n))
    (cp : Vec ℝ n) : -- --- CONCL ---
    hausdorffDist₂
        (Set.linComb H.construct (Zonotope.mtimes (exp (Δtk • A)) H |>.shift (-cp)).construct)
        (H.linComb (Zonotope.mtimes (exp (Δtk • A)) H |>.shift (-cp))).construct
      ≤ Real.sqrt H.h *
        genOpNorm₂ (fun j => (exp (Δtk • A) - 1).mulVec (H.G j)) := by -- --- PROOF ---
  set M : Mat ℝ n n := exp (Δtk • A) with hM
  set H' : Zonotope (Vec ℝ n) := Zonotope.mtimes M H |>.shift (-cp) with hH'
  have hH'h : H'.h = H.h := rfl
  have hH'c : H'.c = M.mulVec H.c + cp := by rw [hH']; simp [Zonotope.shift, Zonotope.mtimes]
  -- a raw `H'.G j` does not itself elaborate once `H'` is `set`-bound, so go through this instead
  have hH'G : ∀ j : Fin H.h, H'.G j = M.mulVec (H.G j) := fun j => rfl
  -- `pairSum`/`pairDiff` collapse since `H.h = H'.h` here — no surplus block either way
  have hpairSum : ∀ j : Fin H.h,
      Zonotope.pairSum H.G H'.G j = (2:ℝ)⁻¹ • (H.G j + M.mulVec (H.G j)) := fun j => by
      rw [show Zonotope.pairSum H.G H'.G j = (2:ℝ)⁻¹ • (H.G j + H'.G j) from by
        simp only [Zonotope.pairSum, hH'h, dif_pos j.isLt, Fin.eta], hH'G j]
  have hpairDiff : ∀ j : Fin H.h,
      Zonotope.pairDiff H.G H'.G j = (2:ℝ)⁻¹ • (H.G j - M.mulVec (H.G j)) := fun j => by
      rw [show Zonotope.pairDiff H.G H'.G j = (2:ℝ)⁻¹ • (H.G j - H'.G j) from by
        simp only [Zonotope.pairDiff, dif_pos j.isLt, Fin.eta], hH'G j]
  have hr : (0:ℝ) ≤ Real.sqrt H.h * genOpNorm₂ (fun j => (M - 1).mulVec (H.G j)) :=
    mul_nonneg (Real.sqrt_nonneg _) (genOpNorm₂_nonneg _)
  refine hausdorffDist₂_le_of_mem_dist hr ?_ ?_
  · -- the exact combination sits inside `linComb`'s own zonotope already
    intro x hx
    exact ⟨x, Zonotope.linComb_outer H H' hx, by rw [sub_self, norm₂_zero]; exact hr⟩
  -- the hard direction: every point of `Ŝ` is within reach of a point of `S`
  intro ŝ hŝ
  obtain ⟨β, hβ, hŝeq⟩ := hŝ
  set βSum : Fin H.h → ℝ := fun j => β (Fin.castAdd 1 (Fin.castAdd H'.h j)) with hβSum
  set βDiff : Fin H.h → ℝ := fun j => β (Fin.castAdd 1 (Fin.natAdd H.h j)) with hβDiff
  set βExtra : ℝ := β (Fin.natAdd (H.h + H'.h) 0) with hβExtra
  -- pointwise, so `simp` can fold a freshly-split `β`-index under a binder into these names
  have hβSum_pt : ∀ j, β (Fin.castAdd 1 (Fin.castAdd H'.h j)) = βSum j := fun j => rfl
  have hβDiff_pt : ∀ j, β (Fin.castAdd 1 (Fin.natAdd H.h j)) = βDiff j := fun j => rfl
  have hβExtra_pt : β (Fin.natAdd (H.h + H'.h) 0) = βExtra := rfl
  have hβSum1 : ∀ j, |βSum j| ≤ 1 := fun j => hβ _
  have hβDiff1 : ∀ j, |βDiff j| ≤ 1 := fun j => hβ _
  have hβExtra1 : |βExtra| ≤ 1 := hβ _
  set lam : ℝ := (1 + βExtra) / 2 with hlam
  have hlam0 : 0 ≤ lam := by rw [hlam]; linarith [(abs_le.mp hβExtra1).1]
  have hlam1 : lam ≤ 1 := by rw [hlam]; linarith [(abs_le.mp hβExtra1).2]
  set x1 : Vec ℝ n := H.c + ∑ j, βSum j • H.G j with hx1
  set x2 : Vec ℝ n := H'.c + ∑ j, βSum j • M.mulVec (H.G j) with hx2
  have hx1mem : x1 ∈ H.construct := ⟨βSum, hβSum1, hx1⟩
  have hx2mem : x2 ∈ H'.construct :=
    ⟨βSum, hβSum1, by rw [hx2]; exact congrArg _ (Finset.sum_congr rfl fun j _ => by
      rw [hH'G j])⟩
  have hsmem : lam • x1 + (1 - lam) • x2 ∈ Set.linComb H.construct H'.construct :=
    ⟨x1, hx1mem, x2, hx2mem, lam, ⟨hlam0, hlam1⟩, rfl⟩
  refine ⟨lam • x1 + (1 - lam) • x2, hsmem, ?_⟩
  -- unwind `ŝ`'s own coordinates: `linComb`'s center and its three generator blocks
  have hŝeq2 : ŝ = (2:ℝ)⁻¹ • (H.c + H'.c) + ∑ j, βSum j • ((2:ℝ)⁻¹ • (H.G j + M.mulVec (H.G j)))
      + ∑ j, βDiff j • ((2:ℝ)⁻¹ • (H.G j - M.mulVec (H.G j)))
      + βExtra • ((2:ℝ)⁻¹ • (H.c - H'.c)) := by
    rw [hŝeq, show (H.linComb H').c = (2:ℝ)⁻¹ • (H.c + H'.c) from rfl,
      aux_sum_univ_linComb2, Fin.sum_univ_add]
    simp only [Zonotope.linComb, Fin.append_left, Fin.append_right, Fin.sum_univ_one,
      hpairSum, hpairDiff, hβSum_pt, hβDiff_pt, hβExtra_pt]
    abel_nf
    ac_rfl
  -- the sign is arranged so the leftover sum needs no separate negation lemma
  have hterm : ∀ j : Fin H.h,
      βSum j • ((2:ℝ)⁻¹ • (H.G j + M.mulVec (H.G j)))
        + βDiff j • ((2:ℝ)⁻¹ • (H.G j - M.mulVec (H.G j)))
        - (lam • (βSum j • H.G j) + (1 - lam) • (βSum j • M.mulVec (H.G j)))
      = (2:ℝ)⁻¹ • ((βExtra * βSum j - βDiff j) • ((M - 1).mulVec (H.G j))) := by
    intro j
    have hMsub : (M - 1).mulVec (H.G j) = M.mulVec (H.G j) - H.G j := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hMsub, hlam]
    -- opaque atoms again, this time so `match_scalars` reads off the coefficient of each cleanly
    generalize H.G j = a
    generalize M.mulVec (H.G j) = b
    generalize βSum j = βS
    generalize βDiff j = βD
    generalize βExtra = βE
    match_scalars <;> ring
  have hdiff : ŝ - (lam • x1 + (1 - lam) • x2)
      = (2:ℝ)⁻¹ • ∑ j, (βExtra * βSum j - βDiff j) • ((M - 1).mulVec (H.G j)) := by
    -- the center terms of `ŝ` and of `lam•x1+(1-lam)•x2` cancel exactly, on their own
    have hcenter : (2:ℝ)⁻¹ • (H.c + H'.c) + βExtra • ((2:ℝ)⁻¹ • (H.c - H'.c))
        - (lam • H.c + (1 - lam) • H'.c) = 0 := by rw [hlam]; module
    -- and the generator terms fold to `hterm`'s target sum, index by index
    have hgen : ∑ j, βSum j • ((2:ℝ)⁻¹ • (H.G j + M.mulVec (H.G j)))
        + ∑ j, βDiff j • ((2:ℝ)⁻¹ • (H.G j - M.mulVec (H.G j)))
        - (∑ j, lam • (βSum j • H.G j) + ∑ j, (1 - lam) • (βSum j • M.mulVec (H.G j)))
        = (2:ℝ)⁻¹ • ∑ j, (βExtra * βSum j - βDiff j) • ((M - 1).mulVec (H.G j)) := by
      -- merge the four sums into one before matching `hterm`'s own per-index statement
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => hterm j
    -- distribute only `lam•x1`/`(1-lam)•x2`, leaving `hŝeq2`'s sums exactly as `hgen` names them
    have hx1lam : lam • x1 = lam • H.c + ∑ j, lam • (βSum j • H.G j) := by
      rw [hx1, smul_add, Finset.smul_sum]
    have hx2lam : (1 - lam) • x2
        = (1 - lam) • H'.c + ∑ j, (1 - lam) • (βSum j • M.mulVec (H.G j)) := by
      rw [hx2, smul_add, Finset.smul_sum]
    rw [hŝeq2, hx1lam, hx2lam]
    -- each generalize turns a sum this equality and `hgen`/`hcenter` both name into one shared atom
    generalize hSA : ∑ j, βSum j • ((2:ℝ)⁻¹ • (H.G j + M.mulVec (H.G j))) = SA at *
    generalize hSB : ∑ j, βDiff j • ((2:ℝ)⁻¹ • (H.G j - M.mulVec (H.G j))) = SB at *
    generalize hSC : ∑ j, lam • (βSum j • H.G j) = SC at *
    generalize hSD : ∑ j, (1 - lam) • (βSum j • M.mulVec (H.G j)) = SD at *
    generalize hSR : (2:ℝ)⁻¹ • ∑ j, (βExtra * βSum j - βDiff j) • ((M - 1).mulVec (H.G j)) = SR at *
    rw [← hgen]
    linear_combination (norm := module) hcenter
  -- fold `hdiff`'s bound back into the Cauchy–Schwarz bound `genOpNorm₂` carries, then `2√γ_h`
  rw [hdiff, norm₂_smul]
  have h1 : |(2:ℝ)⁻¹| = (2:ℝ)⁻¹ := by norm_num
  rw [h1]
  have h2 : ‖∑ j, (βExtra * βSum j - βDiff j) • ((M - 1).mulVec (H.G j))‖₂
      ≤ genOpNorm₂ (fun j => (M - 1).mulVec (H.G j)) * ‖fun j => βExtra * βSum j - βDiff j‖₂ :=
    norm₂_sum_smul_le_genOpNorm₂_mul_norm₂ _ _
  -- `v = βExtra•βSum - βDiff` splits by the triangle inequality into two `√γ_h`-bounded pieces
  have h3 : ‖fun j => βExtra * βSum j - βDiff j‖₂ ≤ 2 * Real.sqrt H.h := by
    calc ‖fun j => βExtra * βSum j - βDiff j‖₂
        ≤ ‖fun j => βExtra * βSum j‖₂ + ‖βDiff‖₂ :=
          norm₂_add_le (fun j => βExtra * βSum j) (fun j => -βDiff j) |>.trans_eq' (by
            congr 1) |>.trans (by
            have hβDiffneg : ‖fun j => -βDiff j‖₂ = ‖βDiff‖₂ := by
              rw [show (fun j => -βDiff j) = (-1:ℝ) • βDiff from by funext j; simp, norm₂_smul]
              norm_num
            rw [hβDiffneg])
      _ ≤ 1 * Real.sqrt H.h + Real.sqrt H.h := by
          gcongr
          · calc ‖fun j => βExtra * βSum j‖₂
                = |βExtra| * ‖βSum‖₂ := by
                  have : (fun j => βExtra * βSum j) = βExtra • βSum := by funext j; rfl
                  rw [this, norm₂_smul]
              _ ≤ 1 * Real.sqrt H.h := mul_le_mul hβExtra1 (aux_norm₂_le_sqrt_card hβSum1)
                  (norm₂_nonneg _) (by norm_num)
          · exact aux_norm₂_le_sqrt_card hβDiff1
      _ = 2 * Real.sqrt H.h := by ring
  -- chain `h2` and `h3` through the outer `(2:ℝ)⁻¹`, landing on `√γ_h · genOpNorm₂` exactly
  calc (2:ℝ)⁻¹ * ‖∑ j, (βExtra * βSum j - βDiff j) • ((M - 1).mulVec (H.G j))‖₂
      ≤ (2:ℝ)⁻¹ * (genOpNorm₂ (fun j => (M - 1).mulVec (H.G j))
          * ‖fun j => βExtra * βSum j - βDiff j‖₂) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ (2:ℝ)⁻¹ * (genOpNorm₂ (fun j => (M - 1).mulVec (H.G j)) * (2 * Real.sqrt H.h)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h3 (genOpNorm₂_nonneg _)) (by norm_num)
    _ = Real.sqrt H.h * genOpNorm₂ (fun j => (M - 1).mulVec (H.G j)) := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
