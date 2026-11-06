module

public import CORALean.ContSet.Zonotope.Float.Operations.ZonotopeNorm
public import CORALean.ContSet.Zonotope.Real.Theorems.ZonotopeNormETop

@[expose] public section

/-!
# `Zonotope.zonotopeNorm` bounds the zonotope norm from below, and `none` is `+∞`

For the real zonotope the stored generators describe, centered at the origin as CORA's
`zonotopeNorm` has it: a returned `t` is at most `‖γ‖∞` for every coefficient vector `γ` with
`G γ = p`, hence at most the extended norm `zonotopeNormE`; and `none` is returned only where
no `γ` reaches `p`, where `zonotopeNormE` is `⊤`, CORA's `Inf`. Every direction `a`, whatever
rounding made of it, gives `|a·p| ≤ ‖γ‖∞ Σ_j |a·g_j|`.

## Inputs
* `Z` – zonotope
* `p` – point

## Hypotheses
* none

## Conclusion
* a returned value is at most the extended zonotope norm of the real zonotope the stored floats
  describe, and `none` implies the norm is `⊤`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       03-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

-- the real zonotope the stored generators describe, centered at the origin
set_option quotPrecheck false in
local notation "ZR[" Z "]" =>
  (Real.Zonotope.mk (Z).h (0 : Vec ℝ (n + 1)) fun j => toRealVec ((Z).G j))


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `|a·p|` is at most `s` times the rounded `Σ_j |a·g_j|`, where `G γ = p` and `|γ_j| ≤ s`. -/
private theorem aux_abs_dot_le (Z : Zonotope (Vec 𝕋 (n + 1))) (a p : Vec 𝕋 (n + 1))
    (γ : Fin Z.h → ℝ) (hγ : ∀ k, ∑ j, toReal (Z.G j k) * γ j = toReal (p k)) (s : ℝ)
    (hs0 : 0 ≤ s) (hs : ∀ j, |γ j| ≤ s) : -- --- CONCL ---
    |∑ k, toReal (a k) * toReal (p k)| ≤ s * toReal (Z.step_dirReach a) := by -- --- PROOF ---
  have hterm : ∀ j, |∑ k, toReal (a k) * toReal (Z.G j k)|
      ≤ toReal (maximum (dotUp a (Z.G j)) (neg (dotDown a (Z.G j)))) := fun j => by
    rw [toReal_maximum, toReal_neg]
    have h1 := le_dotUp a (Z.G j)
    have h2 := dotDown_le a (Z.G j)
    have h3 := le_max_left (toReal (dotUp a (Z.G j))) (-toReal (dotDown a (Z.G j)))
    have h4 := le_max_right (toReal (dotUp a (Z.G j))) (-toReal (dotDown a (Z.G j)))
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  -- `a·p` is the sum of `γ_j (a·g_j)`
  have heq : ∑ k, toReal (a k) * toReal (p k)
      = ∑ j, γ j * ∑ k, toReal (a k) * toReal (Z.G j k) := by
    have : ∀ k, toReal (a k) * toReal (p k)
        = ∑ j, γ j * (toReal (a k) * toReal (Z.G j k)) := fun k => by
      rw [← hγ k, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  -- each term is at most `s` times the rounded `|a·g_j|`
  have hbound : ∀ j, |γ j * ∑ k, toReal (a k) * toReal (Z.G j k)|
      ≤ s * toReal (maximum (dotUp a (Z.G j)) (neg (dotDown a (Z.G j)))) := fun j => by
    rw [abs_mul]
    exact mul_le_mul (hs j) (hterm j) (abs_nonneg _) hs0
  rw [heq]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _)
    (le_trans (Finset.sum_le_sum fun j _ => hbound j) ?_)
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_le_sumUp _) hs0

/-- Every direction's bound is at most the norm of a coefficient vector reaching `p`. -/
private theorem aux_normAt_le (Z : Zonotope (Vec 𝕋 (n + 1))) (p a : Vec 𝕋 (n + 1))
    (γ : Fin Z.h → ℝ) (hγ : ∀ k, ∑ j, toReal (Z.G j k) * γ j = toReal (p k)) (s : ℝ)
    (hs0 : 0 ≤ s) (hs : ∀ j, |γ j| ≤ s) : -- --- CONCL ---
    toReal (Z.step_zonotopeNormAt p a) ≤ s := by -- --- PROOF ---
  unfold Zonotope.step_zonotopeNormAt
  split_ifs with hr
  · have hr' : 0 < toReal (Z.step_dirReach a) := by
      simpa [toReal_zero] using toReal_lt_of_ltStrict hr
    have hab := aux_abs_dot_le Z a p γ hγ s hs0 hs
    have h1 := dotDown_le a p
    have h2 := le_dotUp a p
    rw [toReal_maximum]
    refine max_le ?_ ?_
    · refine le_trans (divDown_le_div _ _ hr') ?_
      rw [div_le_iff₀ hr']
      linarith [le_abs_self (∑ k, toReal (a k) * toReal (p k))]
    · refine le_trans (divDown_le_div _ _ hr') ?_
      rw [div_le_iff₀ hr', toReal_neg]
      linarith [neg_abs_le (∑ k, toReal (a k) * toReal (p k))]
  · rw [toReal_zero]; exact hs0

/-- A folded maximum of such bounds stays below `s`. -/
private theorem aux_foldl_le (Z : Zonotope (Vec 𝕋 (n + 1))) (p : Vec 𝕋 (n + 1)) (s : ℝ)
    (hb : ∀ a, toReal (Z.step_zonotopeNormAt p a) ≤ s) : -- --- CONCL ---
    ∀ (l : List (Vec 𝕋 (n + 1))) (init : 𝕋), toReal init ≤ s →
      toReal (l.foldl (fun best a => maximum best (Z.step_zonotopeNormAt p a)) init)
        ≤ s := by -- --- PROOF ---
  intro l
  induction l with
  | nil => intro init h; exact h
  | cons a l ih =>
    intro init h
    refine ih _ ?_
    rw [toReal_maximum]
    exact max_le h (hb a)


-- =======================================  MAIN THEOREM  ======================================= --

/-- A returned value is at most the extended norm, and `none` is only returned where it is `⊤`. -/
theorem Zonotope.zonotopeNorm_le (Z : Zonotope (Vec 𝕋 (n + 1)))
    (p : Vec 𝕋 (n + 1)) : -- --- CONCL ---
    (∀ t ∈ Z.zonotopeNorm p, ((toReal t : ℝ) : EReal) ≤ ZR[Z].zonotopeNormE (toRealVec p)) ∧
    (Z.zonotopeNorm p = none → ZR[Z].zonotopeNormE (toRealVec p) = ⊤) := by -- --- PROOF ---
  -- a coefficient vector reaching the point, in the stored coordinates
  have hreach : ∀ γ : Vec ℝ ZR[Z].h, ZR[Z].genMap γ = toRealVec p →
      ∀ k, ∑ j, toReal (Z.G j k) * γ j = toReal (p k) := fun γ hγ k => by
    have := congrFun hγ k
    have e : ZR[Z].genMap γ k = ∑ j, toReal (Z.G j k) * γ j := by
      show (∑ j, γ j • toRealVec (Z.G j)) k = _
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => by simp [toRealVec, mul_comm]
    rw [← e, this]
    rfl
  -- no direction certifies `Inf` where a coefficient vector reaches the point
  have hcert : ∀ γ : Vec ℝ ZR[Z].h, ZR[Z].genMap γ = toRealVec p →
      (Z.step_zonotopeNormDirs.any fun a => Z.step_zonotopeNormCert p a) = false := fun γ hγ => by
    rw [Bool.eq_false_iff]
    intro hany
    obtain ⟨a, -, ha⟩ := List.any_eq_true.mp hany
    unfold Zonotope.step_zonotopeNormCert at ha
    rw [Bool.and_eq_true] at ha
    have hs : ∀ j, |γ j| ≤ ‖γ‖ := fun j => by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm γ j
    -- the direction is orthogonal to every generator, so `a·p = 0`
    have hab := aux_abs_dot_le Z a p γ (hreach γ hγ) ‖γ‖ (norm_nonneg _) hs
    have hr := toReal_le_of_le ha.1
    rw [toReal_zero] at hr
    have h0 : |∑ k, toReal (a k) * toReal (p k)| ≤ 0 :=
      hab.trans (mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hr)
    have h0' : ∑ k, toReal (a k) * toReal (p k) = 0 := abs_nonpos_iff.mp h0
    have h1 := dotDown_le a p
    have h2 := le_dotUp a p
    -- which contradicts the certified sign of `a·p`
    rcases Bool.or_eq_true _ _ |>.mp ha.2 with hp | hp
    · have := toReal_lt_of_ltStrict hp
      rw [toReal_zero] at this
      linarith
    · have := toReal_lt_of_ltStrict hp
      rw [toReal_zero] at this
      linarith
  refine ⟨fun t ht => ?_, fun hn => ?_⟩
  · -- a returned value is at most the norm of every coefficient vector reaching the point
    unfold Zonotope.zonotopeNorm at ht
    split_ifs at ht with hany
    · exact absurd ht (by simp)
    rw [Option.mem_def, Option.some.injEq] at ht
    subst ht
    unfold Real.Zonotope.zonotopeNormE
    refine le_sInf ?_
    rintro _ ⟨γ, hγ, rfl⟩
    have hs : ∀ j, |γ j| ≤ ‖γ‖ := fun j => by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm γ j
    refine EReal.coe_le_coe_iff.mpr (aux_foldl_le Z p ‖γ‖ (fun a =>
      aux_normAt_le Z p a γ (hreach γ hγ) ‖γ‖ (norm_nonneg _) hs) _ _ ?_)
    rw [toReal_zero]; exact norm_nonneg _
  · -- `none` is returned only where no coefficient vector reaches the point
    by_cases hex : ∃ γ : Vec ℝ ZR[Z].h, ZR[Z].genMap γ = toRealVec p
    · obtain ⟨γ, hγ⟩ := hex
      have := hcert γ hγ
      unfold Zonotope.zonotopeNorm at hn
      simp [this] at hn
    · exact ZR[Z].zonotopeNormE_eq_top hex

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
