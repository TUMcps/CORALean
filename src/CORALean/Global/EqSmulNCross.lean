import CORALean.Global.CrossProduct

/-!
# The line `nX` spans

[1, Def. 2]'s cross product annihilates the `n` vectors it is built from, and
those leave only a line when they are linearly independent. So any nonzero
vector annihilating all of them is a multiple of `nX(H)` — which is what makes
[1, Thm. 2]'s finitely many normals cover every direction the facets can take.

The scalar comes out of the Gram relation: `(z ⬝ᵥ nX) • z - (z ⬝ᵥ z) • nX`
annihilates `z` and every column, hence the whole space those span, hence
itself, hence is zero.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Module

variable {n : ℕ}


/-- A vector annihilated by a family is annihilated by everything it spans. -/
theorem span_dotProduct_eq_zero {ι : Type} (c : ι → Vec ℝ (n + 1)) (q : Vec ℝ (n + 1))
    (hc : ∀ i, c i ⬝ᵥ q = 0) {x : Vec ℝ (n + 1)}
    (hx : x ∈ Submodule.span ℝ (Set.range c)) : x ⬝ᵥ q = 0 := by -- --- PROOF ---
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hc i
  | zero => simp
  | add y₁ y₂ _ _ h₁ h₂ => rw [add_dotProduct, h₁, h₂, add_zero]
  | smul r y _ h => rw [smul_dotProduct, h, smul_zero]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A nonzero vector annihilating `n` linearly independent vectors is a multiple
of their cross product. -/
theorem eq_smul_nCross (H : Mat ℝ (n + 1) n) (z : Vec ℝ (n + 1)) (hz : z ≠ 0)
    (hcol : ∀ j, (fun i => H i j) ⬝ᵥ z = 0)
    (hind : LinearIndependent ℝ fun j => (fun i => H i j : Vec ℝ (n + 1))) :
    ∃ lam : ℝ, lam ≠ 0 ∧ z = lam • nCross H := by -- --- PROOF ---
  have hzz : z ⬝ᵥ z ≠ 0 := fun h => hz (dotProduct_self_eq_zero.mp h)
  -- `z` and the columns are `n + 1` independent vectors, so a basis
  have hb : LinearIndependent ℝ (Fin.cons z (fun j i => H i j) : Fin (n + 1) → Vec ℝ (n + 1)) :=
    linearIndependent_finCons.mpr ⟨hind, fun hmem => hzz (span_dotProduct_eq_zero _ z hcol hmem)⟩
  have hcard : Fintype.card (Fin (n + 1)) = finrank ℝ (Vec ℝ (n + 1)) := by
    show Fintype.card (Fin (n + 1)) = finrank ℝ (Fin (n + 1) → ℝ)
    simp
  have hspan : Submodule.span ℝ
      (Set.range (Fin.cons z (fun j i => H i j) : Fin (n + 1) → Vec ℝ (n + 1))) = ⊤ := by
    have h := (basisOfLinearIndependentOfCardEqFinrank hb hcard).span_eq
    rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at h
  -- the same family is the columns of `[z | H]`, whose determinant is `z ⬝ᵥ nX(H)`
  have hcols : (Matrix.of fun i => Fin.cons (z i) (H i)).col
      = (Fin.cons z (fun j i => H i j) : Fin (n + 1) → Vec ℝ (n + 1)) := by
    funext j
    refine Fin.cases ?_ (fun j' => ?_) j <;> funext i <;> simp [Matrix.col]
  have hzp : z ⬝ᵥ nCross H ≠ 0 := by
    rw [dotProduct_nCross]
    exact Matrix.isUnit_iff_isUnit_det _ |>.mp
      (Matrix.linearIndependent_cols_iff_isUnit.mp (hcols ▸ hb)) |>.ne_zero
  -- the Gram combination annihilates `z`, every column, and so itself
  set q : Vec ℝ (n + 1) := (z ⬝ᵥ nCross H) • z - (z ⬝ᵥ z) • nCross H with hq
  have hqall : ∀ i, (Fin.cons z (fun j i => H i j) : Fin (n + 1) → Vec ℝ (n + 1)) i ⬝ᵥ q = 0 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, hq, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      ring
    · simp only [Fin.cons_succ, hq, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      rw [hcol j, nCross_dotProduct_col H j, mul_zero, mul_zero, sub_zero]
  have hq0 : q = 0 := by
    refine dotProduct_self_eq_zero.mp (span_dotProduct_eq_zero _ q hqall ?_)
    rw [hspan]
    exact Submodule.mem_top
  -- so `z` and `nX(H)` are proportional, with a scalar the pairing names
  refine ⟨(z ⬝ᵥ z) / (z ⬝ᵥ nCross H), div_ne_zero hzz hzp, ?_⟩
  have hgram : (z ⬝ᵥ nCross H) • z = (z ⬝ᵥ z) • nCross H := by
    rw [← sub_eq_zero]; exact hq0
  rw [div_eq_inv_mul, ← smul_smul, ← hgram, smul_smul, inv_mul_cancel₀ hzp, one_smul]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
