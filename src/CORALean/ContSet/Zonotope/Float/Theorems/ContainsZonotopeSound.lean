module

public import CORALean.ContSet.Zonotope.Float.Operations.ContainsZonotope
public import CORALean.ContSet.Zonotope.Float.Theorems.BallCertReach
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import Mathlib.Data.Matrix.Mul
public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Theorems.ContainsViaReach

@[expose] public section

/-!
# A `true` from `Zonotope.containsZonotope` proves containment

A point of the first set is a nominal point plus a member of its error box. The checked rows are
the hypotheses of `Zonotope.contains_via_reach`, read as reals: the leftover in every entry (center
residual, the row of `|G₁ - G₂ Γ|`, the error box) is at most `B`, a box the right inverse reaches
with coefficients of size at most `δ` (`Zonotope.ballCert_reach`), and the budget
`|β₀ₖ| + ∑ⱼ |Γₖⱼ| + δ` is at most one. The result is a nominal point of the second set moved by the
second error box's lower corner, a member of that box.

## Inputs
* `Z₂` – outer zonotope
* `Z₁` – inner zonotope
* `H` – candidate right inverse

## Hypotheses
* `h` – test returns true

## Conclusion
* inner zonotope is contained in the outer
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `pointLo` and `pointHi` bracket `c + G β`. -/
theorem Zonotope.aux_point_between (Z : Zonotope (Vec 𝕋 n)) (β : Vec 𝕋 Z.h)
    (i : Fin n) : -- --- CONCL ---
    toReal (Z.pointLo β i) ≤ toReal (Z.c i) + ∑ j, toReal (Z.G j i) * toReal (β j)
      ∧ toReal (Z.c i) + ∑ j, toReal (Z.G j i) * toReal (β j)
        ≤ toReal (Z.pointHi β i) := by -- --- PROOF ---
  have h1 := addDown_le_add (Z.c i) (dotDown (fun j => Z.G j i) β)
  have h2 := add_le_addUp (Z.c i) (dotUp (fun j => Z.G j i) β)
  have h3 := dotDown_le (fun j => Z.G j i) β
  have h4 := le_dotUp (fun j => Z.G j i) β
  exact ⟨by simp only [Zonotope.pointLo]; linarith, by simp only [Zonotope.pointHi]; linarith⟩


/-- `aux_mulResidual` bounds `|A - G Γ|`. -/
theorem Zonotope.aux_mulResidual_bound {m h : ℕ} (A : Mat 𝕋 n m) (G : Mat 𝕋 n h) (Γ : Mat 𝕋 h m)
    (i : Fin n) (j : Fin m) : -- --- CONCL ---
    |(toRealMat A - toRealMat G * toRealMat Γ) i j|
      ≤ toReal (Zonotope.aux_mulResidual A G Γ i j) := by -- --- PROOF ---
  have hd := dotDown_le (fun l => G i l) fun l => Γ l j
  have hu := le_dotUp (fun l => G i l) fun l => Γ l j
  have hprod : (toRealMat G * toRealMat Γ) i j = ∑ l, toReal (G i l) * toReal (Γ l j) := rfl
  have h1 := subDown_le_sub (A i j) (dotUp (fun l => G i l) fun l => Γ l j)
  have h2 := sub_le_subUp (A i j) (dotDown (fun l => G i l) fun l => Γ l j)
  rw [Matrix.sub_apply, hprod]
  simp only [Zonotope.aux_mulResidual, toReal_maximum, toReal_absolute]
  have hA : toRealMat A i j = toReal (A i j) := rfl
  rw [hA]
  exact abs_le_max_abs_abs (by linarith) (by linarith)


/-- `aux_errBound` bounds every member of a float box. -/
theorem Zonotope.aux_abs_le_errBound (E : Interval (Vec 𝕋 n)) {e : Vec ℝ n} (he : e ∈ E.construct)
    (i : Fin n) : -- --- CONCL ---
    |e i| ≤ toReal (Zonotope.aux_errBound E i) := by -- --- PROOF ---
  have h1 : toReal (E.inf i) ≤ e i := (he i).1
  have h2 : e i ≤ toReal (E.sup i) := (he i).2
  simp only [Zonotope.aux_errBound, toReal_maximum, toReal_absolute]
  have a1 := neg_abs_le (toReal (E.inf i))
  have a2 := le_abs_self (toReal (E.sup i))
  have m1 := le_max_left |toReal (E.inf i)| |toReal (E.sup i)|
  have m2 := le_max_right |toReal (E.inf i)| |toReal (E.sup i)|
  exact abs_le.mpr ⟨by linarith, by linarith⟩


/-- `aux_entryDeviation` bounds `|x - e - y|`. -/
theorem Zonotope.aux_entryDeviation_bound (x e lo hi : Vec 𝕋 n) {y : ℝ} (i : Fin n)
    (hlo : toReal (lo i) ≤ y) (hhi : y ≤ toReal (hi i)) : -- --- CONCL ---
    |toReal (x i) - toReal (e i) - y|
      ≤ toReal (Zonotope.aux_entryDeviation x e lo hi i) := by -- --- PROOF ---
  have a1 := sub_le_subUp (x i) (e i)
  have a2 := sub_le_subUp (subUp (x i) (e i)) (lo i)
  have b1 := subDown_le_sub (x i) (e i)
  have b2 := sub_le_subUp (hi i) (subDown (x i) (e i))
  simp only [Zonotope.aux_entryDeviation, toReal_maximum]
  have m1 := le_max_left (toReal (subUp (subUp (x i) (e i)) (lo i)))
    (toReal (subUp (hi i) (subDown (x i) (e i))))
  have m2 := le_max_right (toReal (subUp (subUp (x i) (e i)) (lo i)))
    (toReal (subUp (hi i) (subDown (x i) (e i))))
  exact abs_le.mpr ⟨by linarith, by linarith⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.containsZonotope_sound {Z₂ Z₁ : Zonotope (Vec 𝕋 n)} {H : Mat 𝕋 Z₂.h n}
    (h : Z₂.containsZonotope Z₁ H = true) : -- --- CONCL ---
    Z₁.construct ⊆ Z₂.construct := by -- --- PROOF ---
  simp only [Zonotope.containsZonotope, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨⟨hball, hbud⟩, hres⟩, hE⟩ := h
  obtain ⟨-, hreach⟩ := Zonotope.ballCert_reach hball
  -- a point of the first set: nominal part and error part
  intro x hx
  obtain ⟨p, hp, e₁, he₁, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨β, hβ, hp'⟩ := Zonotope.mem_nominalSet_iff.mp hp
  -- the second error box's lower corner, and the real objects
  have he₂ : (fun i => toReal (Z₂.I_error.inf i)) ∈ (I_error Z₂).construct := fun i =>
    ⟨le_refl _, toReal_le_of_le (hE i)⟩
  -- every entry's leftover (center residual, `G₁ - G₂ Γ`, error box) fits in `B`
  have hres' : ∀ i, |toReal (Z₁.c i) - toReal (Z₂.I_error.inf i)
        - (toReal (Z₂.c i) + (toRealMat (fun i j => Z₂.G j i) *ᵥ toRealVec (Z₂.stBeta Z₁ H)) i)|
      + ∑ j, |(toRealMat (fun i j => Z₁.G j i)
          - toRealMat (fun i j => Z₂.G j i) * toRealMat (Z₂.stGamma Z₁ H)) i j|
      + |e₁ i| ≤ toReal (Zonotope.ballB H (Z₂.stDelta Z₁ H)) := by
    intro i
    have a1 := Zonotope.aux_entryDeviation_bound Z₁.c Z₂.I_error.inf (Z₂.pointLo (Z₂.stBeta Z₁ H))
      (Z₂.pointHi (Z₂.stBeta Z₁ H)) i
      (Zonotope.aux_point_between Z₂ (Z₂.stBeta Z₁ H) i).1
      (Zonotope.aux_point_between Z₂ (Z₂.stBeta Z₁ H) i).2
    have a2 : ∑ j, |(toRealMat (fun i j => Z₁.G j i)
          - toRealMat (fun i j => Z₂.G j i) * toRealMat (Z₂.stGamma Z₁ H)) i j|
        ≤ toReal (sumUp fun j => Zonotope.aux_mulResidual (fun i j => Z₁.G j i)
          (fun i j => Z₂.G j i) (Z₂.stGamma Z₁ H) i j) :=
      le_trans (Finset.sum_le_sum fun j _ => Zonotope.aux_mulResidual_bound _ _ _ i j)
        (sum_le_sumUp _)
    have a3 := Zonotope.aux_abs_le_errBound Z₁.I_error he₁ i
    -- the three terms, rounded up, add to at most `B`
    have a4 := toReal_le_of_le (hres i)
    simp only [Zonotope.aux_stLeftover] at a4
    have a5 := add_le_addUp (addUp (Zonotope.aux_entryDeviation Z₁.c Z₂.I_error.inf
      (Z₂.pointLo (Z₂.stBeta Z₁ H)) (Z₂.pointHi (Z₂.stBeta Z₁ H)) i)
      (sumUp fun j => Zonotope.aux_mulResidual (fun i j => Z₁.G j i) (fun i j => Z₂.G j i)
        (Z₂.stGamma Z₁ H) i j))
      (Zonotope.aux_errBound Z₁.I_error i)
    have a6 := add_le_addUp (Zonotope.aux_entryDeviation Z₁.c Z₂.I_error.inf
      (Z₂.pointLo (Z₂.stBeta Z₁ H)) (Z₂.pointHi (Z₂.stBeta Z₁ H)) i)
      (sumUp fun j => Zonotope.aux_mulResidual (fun i j => Z₁.G j i) (fun i j => Z₂.G j i)
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
    (toRealVec Z₁.c) (toRealVec Z₂.c) e₁ (fun i => toReal (Z₂.I_error.inf i))
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
