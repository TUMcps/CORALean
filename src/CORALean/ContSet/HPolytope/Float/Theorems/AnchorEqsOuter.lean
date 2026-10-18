module

public import CORALean.Global.Float.ToRealMatMulVec
public import CORALean.ContSet.HPolytope.Float.Operations.AnchorEqs
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLeft
public import CORALean.ContSet.HPolytope.Float.Theorems.MemNominalIff
public import CORALean.ContSet.Zonotope.Float.Theorems.RightInvGainSolve

@[expose] public section

/-!
# `HPolytope.anchorEqs` contains every point it was given a residual for

A point `y` that satisfies the stored inequalities and reads within `εᵢ` of `beᵢ` on every
equality row, shifted by a point `e` of the error box, lies in the result, on either branch. With
the certificate, `y + δ` is on the stored hyperplanes for the step `δ` with `Ae δ = be - Ae y`,
`|δⱼ| ≤ γ maxᵢ εᵢ ≤ ρ` (`Zonotope.rightInvGain_solve`); each inequality reads at most `∑ⱼ |Aᵢⱼ| ρ`
more on it; and `e - δ` is in the widened box. Without, `y` satisfies the widened pairs and `e` is
in the same box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.anchorEqs_outer (P : HPolytope 𝕋 (Vec 𝕋 n)) (ε : Vec 𝕋 P.me) {y e : Vec ℝ n}
    (hA : ∀ i, (toRealMat P.A *ᵥ y) i ≤ toReal (P.b i) + |toReal (P.b_error i)|)
    (hE : ∀ i, |(toRealMat P.Ae *ᵥ y) i - toReal (P.be i)| ≤ toReal (ε i))
    (he : e ∈ P.I_error.construct) : -- --- STMT ---
    y + e ∈ (P.anchorEqs ε).construct := by -- --- PROOF ---
  unfold HPolytope.anchorEqs
  split
  · rename_i γ hγ
    obtain ⟨hγ0, hsolve⟩ := Zonotope.rightInvGain_solve hγ
    -- the largest residual, which is not negative
    set E := toReal (maximumOver ε) with hEdef
    have hεE : ∀ i, toReal (ε i) ≤ E := fun i => le_maximumOver ε i
    have hE0 : 0 ≤ E := by
      rcases Nat.eq_zero_or_pos P.me with hm | hm
      · have hz : ∀ {k : ℕ} (f : Fin k → 𝕋), k = 0 → toReal (maximumOver f) = 0 := by
          intro k f hk
          subst hk
          exact toReal_zero
        rw [hEdef, hz ε hm]
      · exact le_trans (abs_nonneg _) (le_trans (hE ⟨0, hm⟩) (hεE _))
    -- the step onto the hyperplanes
    obtain ⟨β, hβ, hβB⟩ := hsolve (fun i => toReal (P.be i) - (toRealMat P.Ae *ᵥ y) i) hE0
      fun i => by rw [abs_sub_comm]; exact le_trans (hE i) (hεE i)
    set ρ := mulUp γ (maximumOver ε)
    have hβρ : ∀ j, |β j| ≤ toReal ρ := fun j => le_trans (hβB j) (mul_le_mulUp _ _)
    have hρ0 : 0 ≤ toReal ρ := le_trans (mul_nonneg hγ0 hE0) (mul_le_mulUp _ _)
    have hsplit : y + e = (y + β) + (e - β) := by abel
    rw [hsplit]
    refine Set.add_mem_add (HPolytope.mem_nominal_iff.mpr ⟨fun i => ?_, fun i => ?_⟩) fun j => ?_
    -- an inequality reads at most `∑ⱼ |Aᵢⱼ| ρ` more
    · show (toRealMat P.A *ᵥ (y + β)) i
        ≤ toReal (addUp (P.b i) (mulUp (radius P.A i) ρ)) + |toReal (P.b_error i)|
      have hstep : (toRealMat P.A *ᵥ β) i ≤ toReal (radius P.A i) * toReal ρ :=
        calc (toRealMat P.A *ᵥ β) i = ∑ j, toReal (P.A i j) * β j := rfl
          _ ≤ ∑ j, |toReal (P.A i j)| * toReal ρ := Finset.sum_le_sum fun j _ =>
              le_trans (le_abs_self _) (by
                rw [abs_mul]
                exact mul_le_mul_of_nonneg_left (hβρ j) (abs_nonneg _))
          _ = (∑ j, |toReal (P.A i j)|) * toReal ρ := (Finset.sum_mul _ _ _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right (sum_abs_le_radius i) hρ0
      rw [Matrix.mulVec_add, Pi.add_apply]
      have h1 := mul_le_mulUp (radius P.A i) ρ
      have h2 := add_le_addUp (P.b i) (mulUp (radius P.A i) ρ)
      linarith [hA i]
    -- an equality now holds
    · show |(toRealMat P.Ae *ᵥ (y + β)) i - toReal (P.be i)| ≤ |toReal (FloatOps.zero : 𝕋)|
      rw [Matrix.mulVec_add, Pi.add_apply, hβ, toReal_zero, abs_zero]
      exact (abs_nonpos_iff.mpr (by ring)).trans le_rfl
    -- the box takes the step back
    · have hlo : toReal (P.I_error.inf j) ≤ e j := (he j).1
      have hhi : e j ≤ toReal (P.I_error.sup j) := (he j).2
      have hb := abs_le.mp (hβρ j)
      have h1 := addDown_le_add (P.I_error.inf j) (neg ρ)
      have h2 := add_le_addUp (P.I_error.sup j) ρ
      rw [toReal_neg] at h1
      refine ⟨?_, ?_⟩
      · show toReal (addDown (P.I_error.inf j) (neg ρ)) ≤ e j - β j
        linarith
      · show e j - β j ≤ toReal (addUp (P.I_error.sup j) ρ)
        linarith
  -- without a certificate: the widened pairs, and the same box
  · refine Set.add_mem_add (HPolytope.mem_nominal_iff.mpr ⟨fun k => ?_, fun i => i.elim0⟩) he
    refine Fin.addCases (fun i => ?_) (fun k => ?_) k
    · simp only [HPolytope.mulVec_append_left, Fin.append_left]
      exact hA i
    · have hab := fun i => abs_le.mp (hE i)
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · simp only [toRealMat_append_mulVec_natAdd, HPolytope.mulVec_append_left, Fin.append_left,
          Fin.append_right]
        have h := add_le_addUp (P.be i) (ε i)
        simp only [toReal_zero, abs_zero, add_zero]
        linarith [(hab i).2]
      · simp only [toRealMat_append_mulVec_natAdd, Fin.append_right]
        have hneg : (toRealMat (-P.Ae : Fin P.me → Fin n → 𝕋) *ᵥ y) i = -(toRealMat P.Ae *ᵥ y) i :=
          congrFun (toRealMat_neg_mulVec P.Ae y) i
        have h := add_le_addUp (neg (P.be i)) (ε i)
        rw [toReal_neg] at h
        simp only [toReal_zero, abs_zero, add_zero]
        linarith [(hab i).1]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
