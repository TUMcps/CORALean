import CORALean.ContSet.Zonotope.Float.Operations.ContainsZonotope
import CORALean.ContSet.Zonotope.Float.Theorems.BallCertReach
import CORALean.ContSet.Zonotope.Float.Theorems.EntryDeviationBound
import CORALean.ContSet.Zonotope.Float.Theorems.ErrBoundLe
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Float.Theorems.MulResidualBound
import CORALean.ContSet.Zonotope.Float.Theorems.PointBetween
import CORALean.ContSet.Zonotope.Real.Theorems.ContainsViaReach

/-!
# A `true` from `Zonotope.containsZonotope` proves containment

A point of the first set is a nominal point plus a member of its error box. The checked rows are
the hypotheses of `Zonotope.contains_via_reach`, read as reals: the leftover in every entry (centre
residual, the row of `|G₁ - G₂ Γ|`, the error box) is at most `B`, a box the right inverse reaches
with coefficients of size at most `δ` (`Zonotope.ballCert_reach`), and the budget
`|β₀ₖ| + ∑ⱼ |Γₖⱼ| + δ` is at most one. The result is a nominal point of the second set moved by the
second error box's lower corner, a member of that box.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.containsZonotope_sound {Z₂ Z₁ : Zonotope 𝕋 n} {H : Mat 𝕋 Z₂.h n}
    (h : Z₂.containsZonotope Z₁ H = true) : Z₁.construct ⊆ Z₂.construct := by -- --- PROOF ---
  simp only [Zonotope.containsZonotope, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨⟨hball, hbud⟩, hres⟩, hE⟩ := h
  obtain ⟨-, hreach⟩ := Zonotope.ballCert_reach hball
  -- a point of the first set: nominal part and error part
  intro x hx
  obtain ⟨p, hp, e₁, he₁, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨β, hβ, hp'⟩ := Zonotope.mem_nominalSet_iff.mp hp
  -- the second error box's lower corner, and the real objects
  have he₂ : (fun i => toReal (Z₂.E.inf i)) ∈ (error Z₂).construct := fun i =>
    ⟨le_refl _, toReal_le_of_le (hE i)⟩
  -- every entry's leftover (centre residual, `G₁ - G₂ Γ`, error box) fits in `B`
  have hres' : ∀ i, |toReal (Z₁.c i) - toReal (Z₂.E.inf i)
        - (toReal (Z₂.c i) + (toRealMat (fun i j => Z₂.G j i) *ᵥ toRealVec (Z₂.stBeta Z₁ H)) i)|
      + ∑ j, |(toRealMat (fun i j => Z₁.G j i)
          - toRealMat (fun i j => Z₂.G j i) * toRealMat (Z₂.stGamma Z₁ H)) i j|
      + |e₁ i| ≤ toReal (Zonotope.ballB H (Z₂.stDelta Z₁ H)) := by
    intro i
    have a1 := Zonotope.entryDeviation_bound Z₁.c Z₂.E.inf (Z₂.pointLo (Z₂.stBeta Z₁ H))
      (Z₂.pointHi (Z₂.stBeta Z₁ H)) i
      (Zonotope.point_between Z₂ (Z₂.stBeta Z₁ H) i).1
      (Zonotope.point_between Z₂ (Z₂.stBeta Z₁ H) i).2
    have a2 : ∑ j, |(toRealMat (fun i j => Z₁.G j i)
          - toRealMat (fun i j => Z₂.G j i) * toRealMat (Z₂.stGamma Z₁ H)) i j|
        ≤ toReal (sumUp fun j => Zonotope.mulResidual (fun i j => Z₁.G j i)
          (fun i j => Z₂.G j i) (Z₂.stGamma Z₁ H) i j) :=
      le_trans (Finset.sum_le_sum fun j _ => Zonotope.mulResidual_bound _ _ _ i j)
        (sum_le_sumUp _)
    have a3 := Zonotope.abs_le_errBound Z₁.E he₁ i
    -- the three terms, rounded up, add to at most `B`
    have a4 := toReal_le_of_le (hres i)
    simp only [Zonotope.stLeftover] at a4
    have a5 := add_le_addUp (addUp (Zonotope.entryDeviation Z₁.c Z₂.E.inf
      (Z₂.pointLo (Z₂.stBeta Z₁ H)) (Z₂.pointHi (Z₂.stBeta Z₁ H)) i)
      (sumUp fun j => Zonotope.mulResidual (fun i j => Z₁.G j i) (fun i j => Z₂.G j i)
        (Z₂.stGamma Z₁ H) i j))
      (Zonotope.errBound Z₁.E i)
    have a6 := add_le_addUp (Zonotope.entryDeviation Z₁.c Z₂.E.inf
      (Z₂.pointLo (Z₂.stBeta Z₁ H)) (Z₂.pointHi (Z₂.stBeta Z₁ H)) i)
      (sumUp fun j => Zonotope.mulResidual (fun i j => Z₁.G j i) (fun i j => Z₂.G j i)
        (Z₂.stGamma Z₁ H) i j)
    have a7 : (toRealMat (fun i j => Z₂.G j i) *ᵥ toRealVec (Z₂.stBeta Z₁ H)) i
        = ∑ j, toReal (Z₂.G j i) * toReal (Z₂.stBeta Z₁ H j) := rfl
    rw [a7]
    linarith
  -- the coefficient budget
  have hcoef : ∀ k, |toRealVec (Z₂.stBeta Z₁ H) k| + ∑ j, |toRealMat (Z₂.stGamma Z₁ H) k j|
      + toReal (Z₂.stDelta Z₁ H) ≤ 1 := by
    intro k
    have b1 := toReal_le_of_le (hbud k)
    have b2 := add_le_addUp (Z₂.stUsed Z₁ H k) (Z₂.stDelta Z₁ H)
    have b3 := add_le_addUp (absolute (Z₂.stBeta Z₁ H k))
      (sumUp fun j => absolute (Z₂.stGamma Z₁ H k j))
    have b4 : ∑ j, |toRealMat (Z₂.stGamma Z₁ H) k j|
        ≤ toReal (sumUp fun j => absolute (Z₂.stGamma Z₁ H k j)) := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => (toReal_absolute _).symm)) ?_
      exact sum_le_sumUp _
    have b5 : |toRealVec (Z₂.stBeta Z₁ H) k| = toReal (absolute (Z₂.stBeta Z₁ H k)) :=
      (toReal_absolute _).symm
    rw [toReal_one] at b1
    simp only [Zonotope.stUsed] at b1 b2
    linarith
  -- the real lemma gives coefficients for the second set
  obtain ⟨γ, hγ, hxγ⟩ := CORALean.Real.Zonotope.contains_via_reach (toRealMat (fun i j => Z₁.G j i))
    (toRealMat (fun i j => Z₂.G j i)) (toRealMat (Z₂.stGamma Z₁ H)) (toRealVec (Z₂.stBeta Z₁ H))
    (toRealVec Z₁.c) (toRealVec Z₂.c) e₁ (fun i => toReal (Z₂.E.inf i))
    (fun d hd => by
      obtain ⟨β', h1, h2⟩ := hreach d hd
      exact ⟨β', h1, h2⟩)
    hres' hcoef β hβ
  -- assemble: the point is a nominal point of `Z₂` plus the error corner
  refine Set.mem_add.mpr ⟨toRealVec Z₂.c + toRealMat (fun i j => Z₂.G j i) *ᵥ γ, ?_, _, he₂, ?_⟩
  · exact Zonotope.mem_nominalSet_iff.mpr ⟨γ, hγ, fun i => rfl⟩
  · funext i
    have hi := congrFun hxγ i
    have hp'' := hp' i
    simp only [Pi.add_apply] at hi ⊢
    have hmv : (toRealMat (fun i j => Z₁.G j i) *ᵥ β) i = ∑ j, toReal (Z₁.G j i) * β j := rfl
    rw [hmv] at hi
    have e1 : toRealVec Z₁.c i = toReal (Z₁.c i) := rfl
    have e2 : toRealVec Z₂.c i = toReal (Z₂.c i) := rfl
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
