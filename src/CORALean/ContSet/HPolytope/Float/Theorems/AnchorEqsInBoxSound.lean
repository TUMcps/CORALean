module

public import CORALean.ContSet.HPolytope.Float.Operations.AnchorEqsInBox
public import CORALean.ContSet.HPolytope.Float.Theorems.MemNominalIff
public import CORALean.ContSet.Zonotope.Float.Theorems.RightInvGainSolve

@[expose] public section

/-!
# `HPolytope.anchorEqsInBox` moves a coefficient vector onto the equalities, inside the box

From an accepted certificate: the candidate's exact correction `β̂` solves the stored equalities
with `|β̂ⱼ| ≤ 1 - s`; a coefficient vector `β` of the box that meets the inequalities and reads
within `ε` of the equalities is moved by `δ`, `|δⱼ| ≤ ρ`, onto them; and the point
`β'' = (1 - λ) (β + δ) + λ β̂` at `λ = ρ / (ρ + s)` solves them still, lies in the box, since
`(1 - λ) (1 + ρ) + λ (1 - s) = 1`, and is within `ρ + λ (2 + ρ) ≤ ρ + (ρ / s) (2 + ρ) ≤ τ` of `β`
in every coordinate. The raised inequalities hold at `β''`, each reading at most `∑ⱼ |Aᵢⱼ| τ`
more than at `β`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.anchorEqsInBox_sound {P : HPolytope 𝕋 (Vec 𝕋 n)} {ε : Vec 𝕋 P.me} (β : Vec ℝ n)
    (hβ : ∀ j, |β j| ≤ 1)
    (hA : ∀ k, (toRealMat P.A *ᵥ β) k ≤ toReal (P.b k) + |toReal (P.b_error k)|)
    (hE : ∀ i, |(toRealMat P.Ae *ᵥ β) i - toReal (P.be i)| ≤ toReal (ε i)) : -- --- CONCL ---
    ∀ Q τ, (Q, τ) ∈ P.anchorEqsInBox ε →
      0 ≤ toReal τ ∧ ∃ β'' : Vec ℝ n, (∀ j, |β'' j| ≤ 1) ∧ β'' ∈ Q.nominal.construct
        ∧ ∀ j, |β'' j - β j| ≤ toReal τ := by -- --- PROOF ---
  intro Q τ (h : P.anchorEqsInBox ε = some (Q, τ))
  unfold HPolytope.anchorEqsInBox at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  rename_i γ hγ
  split_ifs at h with hs
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hγ0, hsolve⟩ := Zonotope.rightInvGain_solve hγ
  -- the largest of nonnegative bounds is nonnegative, also over no index at all
  have hmax0 : ∀ {k : ℕ} (f : Fin k → 𝕋), (∀ i, 0 ≤ toReal (f i)) →
      0 ≤ toReal (maximumOver f) := by
    intro k f hf
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      exact le_of_eq toReal_zero.symm
    · exact le_trans (hf ⟨0, hk⟩) (le_maximumOver f _)
  -- names for what the certificate computed
  set M := Zonotope.rightInvCandidate P.Ae
  set β₀ : Vec 𝕋 n := fun j => dotUp (M j) P.be
  set r : Vec 𝕋 P.me := fun i =>
    maximum (subUp (dotUp (P.Ae i) β₀) (P.be i)) (subUp (P.be i) (dotDown (P.Ae i) β₀))
  set s := subDown FloatOps.one
    (addUp (maximumOver fun j => absolute (β₀ j)) (mulUp γ (maximumOver r)))
  set ρ := mulUp γ (maximumOver ε)
  set two := addUp (FloatOps.one : 𝕋) FloatOps.one
  set τ := addUp ρ (mulUp (divUp ρ s) (addUp two ρ))
  have hs0 : 0 < toReal s := by simpa [toReal_zero] using toReal_lt_of_ltStrict hs
  -- the candidate's residual is within `r`
  have hr : ∀ i, |toReal (P.be i) - (toRealMat P.Ae *ᵥ toRealVec β₀) i| ≤ toReal (r i) := by
    intro i
    have h1 := le_dotUp (P.Ae i) β₀
    have h2 := dotDown_le (P.Ae i) β₀
    have h3 := sub_le_subUp (dotUp (P.Ae i) β₀) (P.be i)
    have h4 := sub_le_subUp (P.be i) (dotDown (P.Ae i) β₀)
    have hrow : (toRealMat P.Ae *ᵥ toRealVec β₀) i = ∑ k, toReal (P.Ae i k) * toReal (β₀ k) := rfl
    simp only [r, toReal_maximum]
    rw [hrow, abs_le]
    constructor
    · linarith [le_max_left (toReal (subUp (dotUp (P.Ae i) β₀) (P.be i)))
        (toReal (subUp (P.be i) (dotDown (P.Ae i) β₀)))]
    · linarith [le_max_right (toReal (subUp (dotUp (P.Ae i) β₀) (P.be i)))
        (toReal (subUp (P.be i) (dotDown (P.Ae i) β₀)))]
  have hr0 : 0 ≤ toReal (maximumOver r) := hmax0 r fun i => le_trans (abs_nonneg _) (hr i)
  -- the exact interior point `β̂`, within `1 - s` of the origin
  obtain ⟨δ₀, hδ₀, hδ₀B⟩ := hsolve (fun i => toReal (P.be i) - (toRealMat P.Ae *ᵥ toRealVec β₀) i)
    hr0 fun i => le_trans (hr i) (le_maximumOver r i)
  set βs := toRealVec β₀ + δ₀
  have hβsE : ∀ i, (toRealMat P.Ae *ᵥ βs) i = toReal (P.be i) := fun i => by
    rw [Matrix.mulVec_add, Pi.add_apply, hδ₀]
    ring
  have hβsB : ∀ j, |βs j| ≤ 1 - toReal s := by
    intro j
    have h1 : |toReal (β₀ j)| ≤ toReal (maximumOver fun j => absolute (β₀ j)) := by
      rw [← toReal_absolute]
      exact le_maximumOver (fun j => absolute (β₀ j)) j
    have h2 := mul_le_mulUp γ (maximumOver r)
    have h3 := add_le_addUp (maximumOver fun j => absolute (β₀ j)) (mulUp γ (maximumOver r))
    have h4 := subDown_le_sub FloatOps.one
      (addUp (maximumOver fun j => absolute (β₀ j)) (mulUp γ (maximumOver r)))
    rw [toReal_one] at h4
    calc |βs j| ≤ |toReal (β₀ j)| + |δ₀ j| := abs_add_le _ _
      _ ≤ _ := by linarith [hδ₀B j]
  -- the step `δ` onto the hyperplanes, of size at most `ρ`
  have hε0 : 0 ≤ toReal (maximumOver ε) := hmax0 ε fun i => le_trans (abs_nonneg _) (hE i)
  obtain ⟨δ, hδ, hδB⟩ := hsolve (fun i => toReal (P.be i) - (toRealMat P.Ae *ᵥ β) i) hε0
    fun i => by rw [abs_sub_comm]; exact le_trans (hE i) (le_maximumOver ε i)
  have hδρ : ∀ j, |δ j| ≤ toReal ρ := fun j => le_trans (hδB j) (mul_le_mulUp _ _)
  have hρ0 : 0 ≤ toReal ρ := le_trans (mul_nonneg hγ0 hε0) (mul_le_mulUp _ _)
  -- the pull back towards `β̂`, by `λ = ρ / (ρ + s)`
  set lam := toReal ρ / (toReal ρ + toReal s) with hlam
  have hpos : 0 < toReal ρ + toReal s := by linarith
  have hl0 : 0 ≤ lam := div_nonneg hρ0 hpos.le
  have hl1 : lam * (toReal ρ + toReal s) = toReal ρ := div_mul_cancel₀ _ hpos.ne'
  have hlρ : lam ≤ toReal ρ / toReal s := div_le_div_of_nonneg_left hρ0 hs0 (by linarith)
  have h1l : 0 ≤ 1 - lam := by nlinarith
  set β'' : Vec ℝ n := (1 - lam) • (β + δ) + lam • βs
  have hβ''j : ∀ j, β'' j = (1 - lam) * (β j + δ j) + lam * βs j := fun j => rfl
  -- the move bound `τ`, as computed
  have hτ : toReal ρ + toReal ρ / toReal s * (2 + toReal ρ) ≤ toReal τ := by
    have h1 := div_le_divUp ρ s hs0
    have h2 : toReal (FloatOps.one : 𝕋) + toReal FloatOps.one ≤ toReal two := add_le_addUp _ _
    have h3 := add_le_addUp two ρ
    rw [toReal_one] at h2
    have h4 : toReal ρ / toReal s * (2 + toReal ρ)
        ≤ toReal (divUp ρ s) * toReal (addUp two ρ) :=
      mul_le_mul h1 (by linarith) (by linarith) (le_trans (div_nonneg hρ0 hs0.le) h1)
    have h5 := mul_le_mulUp (divUp ρ s) (addUp two ρ)
    have h6 := add_le_addUp ρ (mulUp (divUp ρ s) (addUp two ρ))
    linarith
  -- every coordinate moves by at most `τ`
  have hmove : ∀ j, |β'' j - β j| ≤ toReal τ := by
    intro j
    have hsplit : β'' j - β j = δ j + lam * (βs j - (β j + δ j)) := by rw [hβ''j]; ring
    have hfar : |βs j - (β j + δ j)| ≤ 2 + toReal ρ := by
      calc |βs j - (β j + δ j)| ≤ |βs j| + (|β j| + |δ j|) :=
            le_trans (abs_sub _ _) (add_le_add_right (abs_add_le _ _) _)
        _ ≤ _ := by linarith [hβsB j, hβ j, hδρ j]
    have hlam : lam * |βs j - (β j + δ j)| ≤ toReal ρ / toReal s * (2 + toReal ρ) :=
      mul_le_mul hlρ hfar (abs_nonneg _) (div_nonneg hρ0 hs0.le)
    rw [hsplit]
    calc |δ j + lam * (βs j - (β j + δ j))| ≤ |δ j| + lam * |βs j - (β j + δ j)| := by
          refine le_trans (abs_add_le _ _) ?_
          rw [abs_mul, abs_of_nonneg hl0]
      _ ≤ _ := by linarith [hδρ j]
  have hτ0 : 0 ≤ toReal τ := le_trans (by positivity) hτ
  refine ⟨hτ0, β'', fun j => ?_, HPolytope.mem_nominal_iff.mpr ⟨fun k => ?_, fun i => ?_⟩, hmove⟩
  -- in the box: `(1 - λ) (1 + ρ) + λ (1 - s) = 1`
  · rw [hβ''j]
    have h1 : |β j + δ j| ≤ 1 + toReal ρ := le_trans (abs_add_le _ _) (by linarith [hβ j, hδρ j])
    calc |(1 - lam) * (β j + δ j) + lam * βs j|
        ≤ (1 - lam) * |β j + δ j| + lam * |βs j| := by
          refine le_trans (abs_add_le _ _) ?_
          rw [abs_mul, abs_mul, abs_of_nonneg h1l, abs_of_nonneg hl0]
      _ ≤ (1 - lam) * (1 + toReal ρ) + lam * (1 - toReal s) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 h1l) (mul_le_mul_of_nonneg_left (hβsB j) hl0)
      _ = 1 := by linarith
  -- an inequality reads at most `∑ⱼ |Aₖⱼ| τ` more than at `β`
  · show (toRealMat P.A *ᵥ β'') k
      ≤ toReal (P.b k) + |toReal (addUp (absolute (P.b_error k)) (mulUp (radius P.A k) τ))|
    have hd : (toRealMat P.A *ᵥ (β'' - β)) k ≤ toReal (radius P.A k) * toReal τ :=
      calc (toRealMat P.A *ᵥ (β'' - β)) k = ∑ j, toReal (P.A k j) * (β'' - β) j := rfl
        _ ≤ ∑ j, |toReal (P.A k j)| * toReal τ := Finset.sum_le_sum fun j _ =>
            le_trans (le_abs_self _) (by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hmove j) (abs_nonneg _))
        _ = (∑ j, |toReal (P.A k j)|) * _ := (Finset.sum_mul _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (sum_abs_le_radius k) hτ0
    have hsum : (toRealMat P.A *ᵥ β'') k
        = (toRealMat P.A *ᵥ β) k + (toRealMat P.A *ᵥ (β'' - β)) k := by
      rw [Matrix.mulVec_sub, Pi.sub_apply]
      ring
    have h1 := mul_le_mulUp (radius P.A k) τ
    have h2 := add_le_addUp (absolute (P.b_error k)) (mulUp (radius P.A k) τ)
    rw [toReal_absolute] at h2
    -- the row at `β`, plus the move
    rw [hsum]
    linarith [hA k, le_abs_self (toReal (addUp (absolute (P.b_error k)) (mulUp (radius P.A k) τ)))]
  -- the equalities hold at both ends of the segment, so along it
  · show |(toRealMat P.Ae *ᵥ β'') i - toReal (P.be i)| ≤ |toReal (FloatOps.zero : 𝕋)|
    rw [toReal_zero, abs_zero, abs_nonpos_iff, sub_eq_zero]
    have hβ' : (toRealMat P.Ae *ᵥ (β + δ)) i = toReal (P.be i) := by
      rw [Matrix.mulVec_add, Pi.add_apply, hδ]
      ring
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
      Pi.smul_apply, smul_eq_mul, smul_eq_mul, hβ', hβsE i]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
