module

public import CORALean.ContSet.SpectraShadow.Real.Operations.GenerateESumRep
public import CORALean.ContSet.SpectraShadow.Real.Theorems.EqBlockSum

@[expose] public section

/-!
# The existential sum representation denotes the same set

`generateESumRep S` stands for exactly the set of `S`: its inequality is the shadow's, side by side
with the diagonal pair `x - c - G β ⪰ 0`, `-(x - c - G β) ⪰ 0`, which holds only at `x = c + G β`.

## Inputs
* `S` – spectrahedral shadow

## Hypotheses
* none

## Conclusion
* the existential sum representation denotes the same set
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem SpectraShadow.aux_lmi_esum (S : SpectraShadow (Vec ℝ n)) (x : Vec ℝ n)
    (y : Fin S.m → ℝ) : -- --- CONCL ---
    S.generateESumRep.B₀ + ∑ i, x i • S.generateESumRep.B i
        + ∑ j : Fin S.generateESumRep.q, y j • S.generateESumRep.C j
      = blockDiag 0 (S.A₀ + ∑ j, y j • S.A j)
        (blockDiag 0 (diagonal (x - S.c - ∑ j, y j • S.G j))
          (diagonal (-(x - S.c - ∑ j, y j • S.G j)))) := by -- --- PROOF ---
  -- a weighted sum of block-diagonal matrices is the block diagonal of the weighted sums
  have hcomb : ∀ {ι : Type} (u : Finset ι) (w : ι → ℝ) {a b : ℕ} (X : ι → Mat ℝ a a)
      (Y : ι → Mat ℝ b b), ∑ i ∈ u, w i • blockDiag 0 (X i) (Y i)
        = blockDiag 0 (∑ i ∈ u, w i • X i) (∑ i ∈ u, w i • Y i) := by
    intro ι u w a b X Y
    simp_rw [← blockDiag_smul]
    rw [← blockDiag_sum]
  -- the point's own coordinates `x`, as the sum of the unit vectors they weigh
  have hx : x = ∑ i, x i • (Pi.single i 1 : Vec ℝ n) := by
    ext r
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : ∑ i, x i • S.generateESumRep.B i
      = blockDiag 0 (0 : Mat ℝ S.k S.k)
        (blockDiag 0 (diagonal x) (diagonal (-x))) := by
    simp only [SpectraShadow.generateESumRep]
    rw [hcomb, SpectraShadow.eq_block_sum (Finset.univ) x (fun i => (Pi.single i 1 : Vec ℝ n)),
      ← hx]
    simp
  -- the existential variables carry the shadow's inequality and the equality's generators
  have h2 : ∑ j : Fin S.generateESumRep.q, y j • S.generateESumRep.C j
      = blockDiag 0 (∑ j, y j • S.A j)
        (blockDiag 0 (diagonal (∑ j, y j • (-S.G j)))
          (diagonal (-(∑ j, y j • (-S.G j))))) := by
    simp only [SpectraShadow.generateESumRep]
    rw [hcomb, SpectraShadow.eq_block_sum (Finset.univ) y (fun j => -S.G j)]
  -- gather the constant, point and existential parts into one block diagonal
  rw [h1, h2]
  simp only [SpectraShadow.generateESumRep]
  rw [← blockDiag_add, ← blockDiag_add]
  congr 1
  · simp
  · rw [← blockDiag_add, ← blockDiag_add]
    congr 1 <;> (ext j k; by_cases hjk : j = k <;> simp [hjk]; ring)


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.generateESumRep_exact (S : SpectraShadow (Vec ℝ n)) : -- --- CONCL ---
    S.generateESumRep.construct = S.construct := by -- --- PROOF ---
  ext x
  constructor
  -- the inequality holds only if the shadow's does and `x - c - G y` is both `≥ 0` and `≤ 0`
  · rintro ⟨y, hy⟩
    rw [SpectraShadow.aux_lmi_esum, posSemidef_blockDiag_iff, posSemidef_blockDiag_iff,
      posSemidef_diagonal_iff, posSemidef_diagonal_iff] at hy
    obtain ⟨hA, h1, h2⟩ := hy
    refine ⟨y, hA, ?_⟩
    ext r
    have a := h1 r
    have b := h2 r
    simp only [Pi.neg_apply, Pi.sub_apply] at a b
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
    linarith
  -- at `y = β` the equality block is the zero matrix
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨β, ?_⟩
    rw [SpectraShadow.aux_lmi_esum]
    have : (S.c + ∑ j, β j • S.G j) - S.c - ∑ j, β j • S.G j = 0 := by abel
    rw [this]
    refine (posSemidef_blockDiag_iff _ _).2 ⟨hβ, ?_⟩
    have h0 : blockDiag 0 (diagonal (0 : Vec ℝ n)) (diagonal (-(0 : Vec ℝ n))) = 0 := by
      simp [blockDiag_zero]
    rw [h0]
    exact PosSemidef.zero

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
