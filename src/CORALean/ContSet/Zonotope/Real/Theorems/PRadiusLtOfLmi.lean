module

public import CORALean.ContSet.Zonotope.Real.Definitions.PRadius
public import CORALean.Global.PosDefSchurComplement
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# The online W-radius bound

[1, Thm. 4], corrected: if `W ≻ 0` and a diagonal `M = diag(m)` satisfy `[M ⋆; W Ĥ W] ≻ 0` Eq. 27 of
[1, Thm. 4], `Ĥ` the generator matrix of the zonotope, then its W-radius is below `max_{z ∈ B} zᵀ M
z = Σᵢ mᵢ = tr M`, the quantity [1, Eq. 29] minimizes. The paper prints the bound Eq. 28 of [1, Thm.
4] as `max_z ‖M z‖²₂ = Σᵢ mᵢ²`, which is false (`pRadius_lt_of_lmi_counterexample`); its own proof
establishes `zᵀ Ĥᵀ W Ĥ z < zᵀ M z`, which is this. `M`'s size is the generator count, not `n_x ×
n_x` as printed. At least one generator is needed for the strict inequality.

The Schur complement of the block `W` gives `M - Ĥᵀ W Ĥ ≻ 0`, so every point `c + Ĥ b`, `b ≠ 0`,
has `‖Ĥ b‖²_W < Σ mᵢ bᵢ² ≤ Σ mᵢ`, each `mᵢ` positive; the box is compact, so the supremum is a
point's value and the bound stays strict.

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.pRadius_lt_of_lmi (W : Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) (m : Vec ℝ Z.h)
    (hW : W.PosDef)
    (hLMI :
      let H : Matrix (Fin n) (Fin Z.h) ℝ := Matrix.of fun i j => Z.G j i
      (fromBlocks (diagonal m) (W * H)ᵀ (W * H) W).PosDef)
    (hh : 0 < Z.h) : -- --- STMT ---
    Z.pRadius W < ∑ i, m i := by -- --- PROOF ---
  set H : Matrix (Fin n) (Fin Z.h) ℝ := Matrix.of fun i j => Z.G j i
  haveI : Invertible W := hW.isUnit.invertible
  have hWT : Wᵀ = W := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hW.isHermitian.eq
  -- the Schur complement: `M - Ĥᵀ W Ĥ ≻ 0`
  have hS : (diagonal m - Hᵀ * W * H).PosDef := by
    have h := posDef_schur_of_fromBlocks (diagonal m) (W * H)ᵀ hW
      (by rw [transpose_transpose]; exact hLMI)
    rwa [transpose_transpose, transpose_mul, hWT, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc W⁻¹, inv_mul_of_invertible, Matrix.one_mul, ← Matrix.mul_assoc] at h
  have hHb : ∀ b : Fin Z.h → ℝ, ∑ j, b j • Z.G j = H *ᵥ b := fun b => by
    ext i; simp [H, Matrix.mulVec, dotProduct, mul_comm]
  -- a nonzero coefficient vector: `‖Ĥ b‖²_W < Σ mᵢ bᵢ²`
  have hlt : ∀ b : Fin Z.h → ℝ, b ≠ 0 →
      (H *ᵥ b) ⬝ᵥ (W *ᵥ (H *ᵥ b)) < ∑ i, m i * b i ^ 2 := fun b hb => by
    have h := (posDef_iff_dotProduct_mulVec.mp hS).2 hb
    rw [star_trivial, sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec b Hᵀ, vecMul_transpose] at h
    have hd : b ⬝ᵥ (diagonal m *ᵥ b) = ∑ i, m i * b i ^ 2 := by
      simp only [dotProduct, mulVec_diagonal]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  have hm : ∀ i, 0 < m i := fun i => by
    have h := hlt (Pi.single i 1) (by simp)
    have h0 := (posSemidef_iff_dotProduct_mulVec.mp hW.posSemidef).2 (H *ᵥ Pi.single i 1)
    rw [star_trivial] at h0
    have hs : ∑ k, m k * (Pi.single i (1 : ℝ) : Fin Z.h → ℝ) k ^ 2 = m i := by
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]; simp
    linarith
  -- the values form the image of the compact box
  set f : (Fin Z.h → ℝ) → ℝ := fun b => (∑ j, b j • Z.G j) ⬝ᵥ (W *ᵥ ∑ j, b j • Z.G j)
  have himg : (fun z => (z - Z.c) ⬝ᵥ (W *ᵥ (z - Z.c))) '' Z.construct =
      f '' {b | ∀ j, |b j| ≤ 1} := by
    ext r
    simp only [Set.mem_image, Zonotope.construct, Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨b, hb, by simp [f]⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨_, ⟨b, hb, rfl⟩, by simp [f]⟩
  have hbox : IsCompact {b : Fin Z.h → ℝ | ∀ j, |b j| ≤ 1} := by
    have : {b : Fin Z.h → ℝ | ∀ j, |b j| ≤ 1} = Set.univ.pi fun _ => Set.Icc (-1) 1 := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]
    rw [this]; exact isCompact_univ_pi fun _ => isCompact_Icc
  have hf : Continuous f := by fun_prop
  have hne : (f '' {b | ∀ j, |b j| ≤ 1}).Nonempty := ⟨f 0, 0, by simp, rfl⟩
  obtain ⟨b, hb, heq⟩ := (hbox.image hf).sSup_mem hne
  rw [Zonotope.pRadius, himg, ← heq]
  simp only [f, hHb]
  -- the maximizer: zero, or a nonzero `b` with `Σ mᵢ bᵢ² ≤ Σ mᵢ`
  by_cases hb0 : b = 0
  · subst hb0
    haveI : Nonempty (Fin Z.h) := ⟨⟨0, hh⟩⟩
    simpa using Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty
  · refine (hlt b hb0).trans_le (Finset.sum_le_sum fun i _ => ?_)
    exact mul_le_of_le_one_right (hm i).le ((sq_le_one_iff_abs_le_one _).mpr (hb i))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
