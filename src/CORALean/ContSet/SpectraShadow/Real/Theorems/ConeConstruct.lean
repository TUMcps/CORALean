import CORALean.ContSet.SpectraShadow.Real.Operations.Cone
import CORALean.ContSet.SpectraShadow.Real.Theorems.ArrowMatPosSemidefOfPos
import CORALean.ContSet.SpectraShadow.Real.Theorems.ArrowMatPosSemidefZero
import CORALean.ContSet.SpectraShadow.Real.Theorems.ArrowMatPosSemidefNecessary

/-!
# The cone of a shadow is the perspective cone with its apex

For a shadow `T` of `ℝ^N`, `N ≥ 1`, `SpectraShadow.cone T` is exactly the set of `s x` for
`s > 0` and `x` in `T`, together with the origin: the points on the open rays through the
shadow, and the apex, which is what [[t, zᵀ], [z, s I]] ⪰ 0 allows at `s = 0`. Not closed: it
contains no recession direction of `T`, which is why the convex hull built from two of these is
exact and not a closure.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix CORALean

variable {N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_arrowMat_add (s s' t t' : ℝ) (w w' : Vec ℝ N) :
    arrowMat (s + s') (t + t') (w + w') = arrowMat s t w + arrowMat s' t' w' := by
  ext p q
  refine Fin.cases ?_ (fun i => ?_) p <;> refine Fin.cases ?_ (fun j => ?_) q <;>
    simp [arrowMat]
  · split_ifs <;> ring

theorem aux_arrowMat_smul (r s t : ℝ) (w : Vec ℝ N) :
    arrowMat (r * s) (r * t) (r • w) = r • arrowMat s t w := by
  ext p q
  refine Fin.cases ?_ (fun i => ?_) p <;> refine Fin.cases ?_ (fun j => ?_) q <;>
    simp [arrowMat]

theorem aux_arrowMat_zero : arrowMat 0 0 (0 : Vec ℝ N) = 0 := by
  ext p q
  refine Fin.cases ?_ (fun i => ?_) p <;> refine Fin.cases ?_ (fun j => ?_) q <;>
    simp [arrowMat]

theorem aux_arrowMat_sum {ι : Type} (u : Finset ι) (a b : ι → ℝ) (w : ι → Vec ℝ N) :
    arrowMat (∑ i ∈ u, a i) (∑ i ∈ u, b i) (∑ i ∈ u, w i)
      = ∑ i ∈ u, arrowMat (a i) (b i) (w i) := by -- --- PROOF ---
  classical
  induction u using Finset.induction_on with
  | empty => simpa using aux_arrowMat_zero
  | insert i u hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi,
      aux_arrowMat_add, ih]

theorem SpectraShadow.aux_lmi_cone (T : SpectraShadow (Vec ℝ N)) (s t : ℝ) (β : Fin T.m → ℝ) :
    (0 : Mat ℝ (T.k + (N + 1)) (T.k + (N + 1))) + ∑ i : Fin (1 + T.m + 1),
        (Fin.append (Fin.append (fun _ : Fin 1 => s) β) (fun _ : Fin 1 => t) :
          Fin (1 + T.m + 1) → ℝ) i •
        (Fin.append
          (Fin.append (fun _ : Fin 1 => blockDiag 0 T.A₀ (arrowMat 1 0 T.c))
            (fun j => blockDiag 0 (T.A j) (arrowMat 0 0 (T.G j))))
          (fun _ : Fin 1 => blockDiag 0 0 (arrowMat 0 1 0)) :
          Fin (1 + T.m + 1) → Mat ℝ (T.k + (N + 1)) (T.k + (N + 1))) i
      = blockDiag 0 (s • T.A₀ + ∑ j, β j • T.A j)
          (arrowMat s t (s • T.c + ∑ j, β j • T.G j)) := by -- --- PROOF ---
  -- the three layers of the sum, the scaled blocks gathered into one block diagonal
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.sum_univ_one]
  simp only [← blockDiag_smul]
  rw [← blockDiag_sum, zero_add, ← blockDiag_add, ← blockDiag_add]
  congr 1
  · simp
  -- the arrowhead block is linear in `(s, t, w)`, so its scaled pieces add to the arrowhead
  · have e1 : s • arrowMat 1 0 T.c = arrowMat s 0 (s • T.c) := by
      rw [← aux_arrowMat_smul]; simp
    have e2 : ∀ j, β j • arrowMat 0 0 (T.G j) = arrowMat 0 0 (β j • T.G j) := fun j => by
      rw [← aux_arrowMat_smul]; simp
    have e3 : t • arrowMat 0 1 (0 : Vec ℝ N) = arrowMat 0 t 0 := by
      rw [← aux_arrowMat_smul]; simp
    rw [e1, e3]
    simp only [e2]
    -- the sum of the generator pieces
    have := aux_arrowMat_sum (Finset.univ : Finset (Fin T.m)) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
      (fun j => β j • T.G j)
    simp only [Finset.sum_const_zero] at this
    rw [← this, ← aux_arrowMat_add, ← aux_arrowMat_add]
    simp

theorem SpectraShadow.aux_gen_cone (T : SpectraShadow (Vec ℝ N)) (s t : ℝ) (β : Fin T.m → ℝ) :
    (0 : Vec ℝ N) + ∑ i : Fin (1 + T.m + 1),
        (Fin.append (Fin.append (fun _ : Fin 1 => s) β) (fun _ : Fin 1 => t) :
          Fin (1 + T.m + 1) → ℝ) i •
        (Fin.append (Fin.append (fun _ : Fin 1 => T.c) T.G) (fun _ : Fin 1 => (0 : Vec ℝ N)) :
          Fin (1 + T.m + 1) → Vec ℝ N) i
      = s • T.c + ∑ j, β j • T.G j := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.sum_univ_one, smul_zero, add_zero, zero_add]

theorem aux_eq_append3 {m : ℕ} (b : Fin (1 + m + 1) → ℝ) :
    b = Fin.append (Fin.append (fun _ : Fin 1 => b (Fin.castAdd 1 (Fin.castAdd m 0)))
      (fun j => b (Fin.castAdd 1 (Fin.natAdd 1 j))))
      (fun _ : Fin 1 => b (Fin.natAdd (1 + m) 0)) := by -- --- PROOF ---
  funext i
  induction i using Fin.addCases with
  | left p =>
    induction p using Fin.addCases with
    | left a =>
      obtain rfl : a = 0 := Subsingleton.elim _ _
      simp
    | right c => simp
  | right q =>
    obtain rfl : q = 0 := Subsingleton.elim _ _
    simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.cone_construct (hN : 0 < N) (T : SpectraShadow (Vec ℝ N)) :
    T.cone.construct
      = {z | z = 0 ∨ ∃ s : ℝ, 0 < s ∧ ∃ x ∈ T.construct, z = s • x} := by -- --- PROOF ---
  ext z
  constructor
  -- a point of the cone: split its variables into `s`, `β` and `t`
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨s, β, t, rfl⟩ : ∃ (s : ℝ) (β : Fin T.m → ℝ) (t : ℝ), b = Fin.append
        (Fin.append (fun _ : Fin 1 => s) β) (fun _ : Fin 1 => t) :=
      ⟨_, _, _, aux_eq_append3 b⟩
    -- the inequality is the shadow's scaled by `s`, beside the arrowhead block
    have hb2 : (blockDiag 0 (s • T.A₀ + ∑ j, β j • T.A j)
        (arrowMat s t (s • T.c + ∑ j, β j • T.G j))).PosSemidef := by
      rw [← SpectraShadow.aux_lmi_cone]
      exact hb
    have hz : T.cone.c + ∑ i : Fin T.cone.m, (Fin.append (Fin.append (fun _ : Fin 1 => s) β)
        (fun _ : Fin 1 => t) : Fin (1 + T.m + 1) → ℝ) i • T.cone.G i
        = s • T.c + ∑ j, β j • T.G j := by
      rw [← SpectraShadow.aux_gen_cone T s t β]
      rfl
    rw [hz]
    obtain ⟨hA, hArrow⟩ := (posSemidef_blockDiag_iff _ _).1 hb2
    -- `s ≥ 0`, and the point is `0` at `s = 0`
    obtain ⟨hs, hs0⟩ := arrowMat_posSemidef_necessary hN hArrow
    rcases hs.eq_or_lt with h | h
    · exact Or.inl (hs0 h.symm)
    -- at `s > 0` the point is `s x` for `x` in the shadow at the coefficients `β / s`
    · refine Or.inr ⟨s, h, T.c + ∑ j, (β j / s) • T.G j, ⟨fun j => β j / s, ?_, rfl⟩, ?_⟩
      · have := hA.smul (inv_nonneg.2 h.le)
        convert this using 1
        simp only [smul_add, smul_smul, Finset.smul_sum, inv_mul_cancel₀ h.ne', one_smul,
          div_eq_inv_mul]
      · simp only [smul_add, Finset.smul_sum, smul_smul]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_div_cancel₀ _ h.ne']
  -- the origin is at `s = t = 0`, a point `s x` at `s`, `s γ` and `t = ‖z‖² / s`
  · rintro (rfl | ⟨s, hs, x, ⟨γ, hγ, rfl⟩, rfl⟩)
    · refine ⟨Fin.append (Fin.append (fun _ : Fin 1 => 0) (fun _ : Fin T.m => 0))
        (fun _ : Fin 1 => 0), ?_, ?_⟩
      · have : (blockDiag 0 ((0 : ℝ) • T.A₀ + ∑ j, (0 : ℝ) • T.A j)
            (arrowMat 0 0 ((0 : ℝ) • T.c + ∑ j, (0 : ℝ) • T.G j))).PosSemidef := by
          simp only [zero_smul, Finset.sum_const_zero, add_zero, aux_arrowMat_zero,
            blockDiag_zero]
          exact PosSemidef.zero
        rw [← SpectraShadow.aux_lmi_cone] at this
        exact this
      · have := SpectraShadow.aux_gen_cone T 0 0 (fun _ => 0)
        simp only [zero_smul, Finset.sum_const_zero, add_zero] at this
        exact this.symm
    -- the point `z = s x` at the coefficients `s γ`
    · set z : Vec ℝ N := s • (T.c + ∑ j, γ j • T.G j) with hzdef
      refine ⟨Fin.append (Fin.append (fun _ : Fin 1 => s) (fun j => s * γ j))
        (fun _ : Fin 1 => (z ⬝ᵥ z) / s), ?_, ?_⟩
      · have hz : s • T.c + ∑ j, (s * γ j) • T.G j = z := by
          simp only [hzdef, smul_add, Finset.smul_sum, smul_smul]
        -- the shadow's inequality scaled by `s`, and the arrowhead at `t = ‖z‖² / s`
        have : (blockDiag 0 (s • T.A₀ + ∑ j, (s * γ j) • T.A j)
            (arrowMat s ((z ⬝ᵥ z) / s) (s • T.c + ∑ j, (s * γ j) • T.G j))).PosSemidef := by
          rw [hz]
          refine (posSemidef_blockDiag_iff _ _).2 ⟨?_, arrowMat_posSemidef_of_pos hs ?_⟩
          · have := hγ.smul hs.le
            convert this using 1
            simp only [smul_add, Finset.smul_sum, smul_smul]
          · rw [mul_div_cancel₀ _ hs.ne']
        rw [← SpectraShadow.aux_lmi_cone] at this
        exact this
      · have := SpectraShadow.aux_gen_cone T s ((z ⬝ᵥ z) / s) (fun j => s * γ j)
        have hz : s • T.c + ∑ j, (s * γ j) • T.G j = z := by
          simp only [hzdef, smul_add, Finset.smul_sum, smul_smul]
        rw [hz] at this
        exact this.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
