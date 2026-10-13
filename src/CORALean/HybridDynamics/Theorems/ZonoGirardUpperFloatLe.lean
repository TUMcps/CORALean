import CORALean.HybridDynamics.Operations.ZonoGirardUpperFloat

/-!
# The dual bound of `Location.zonoGirardUpperFloat` holds

The plane image of a state on the hyperplane is `(γ, x·ℓ)`, a point of the plane zonotope, which
the rounded support function bounds in the direction `(-μ, 1)`; `x·ℓ = (x·ℓ - μγ) + μγ` and
`μγ` is below `mulUp μ γ`, so every dual value bounds `x·ℓ`, and so does the least of them.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps CORALean.Float.SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state of `Z` on the hyperplane is below `zonoGirardUpperFloat` along `ℓ`. -/
theorem Location.zonoGirardUpperFloat_le (Z : Zonotope (Vec 𝕋 n)) (nv : Vec 𝕋 n) (γ : 𝕋)
    (ℓ : Vec 𝕋 n) {x : Vec ℝ n} (hx : x ∈ Z.construct)
    (hg : x ⬝ᵥ toRealVec nv = toReal γ) :
    x ⬝ᵥ toRealVec ℓ ≤ toReal (Location.zonoGirardUpperFloat Z nv γ ℓ) := by -- --- PROOF ---
  unfold Location.zonoGirardUpperFloat
  -- the plane image of `x` lies in the plane zonotope
  have hy := Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k))
    (fun (i : Fin 2) (j : Fin n) => if i = 0 then nv j else ℓ j) Z
    (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx))
  generalize Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k))
    (fun (i : Fin 2) (j : Fin n) => if i = 0 then nv j else ℓ j) Z = S at hy ⊢
  have h0 : (Scalar.toRealMat (fun (i : Fin 2) (j : Fin n) => if i = 0 then nv j else ℓ j) *ᵥ x) 0
      = toReal γ := by
    rw [← hg, dotProduct_comm]
    simp [Matrix.mulVec, dotProduct, Scalar.toRealMat_apply, toRealVec]
    rfl
  have h1 : (Scalar.toRealMat (fun (i : Fin 2) (j : Fin n) => if i = 0 then nv j else ℓ j) *ᵥ x) 1
      = x ⬝ᵥ toRealVec ℓ := by
    rw [dotProduct_comm]
    simp [Matrix.mulVec, dotProduct, Scalar.toRealMat_apply, toRealVec]
    rfl
  generalize Scalar.toRealMat (fun (i : Fin 2) (j : Fin n) => if i = 0 then nv j else ℓ j) *ᵥ x
    = y at hy h0 h1
  -- the dual bound at a multiplier `μ`
  have hdual : ∀ μ : 𝕋, x ⬝ᵥ toRealVec ℓ ≤ toReal (addUp
      (S.boundDot (c := rowLin (fun _ : Fin 1 => ![neg μ, one]) 0) ![neg μ, one]
        (fun _ => rfl)).val (mulUp μ γ)) := fun μ => by
    have hb := (S.boundDot (c := rowLin (fun _ : Fin 1 => ![neg μ, one]) 0) ![neg μ, one]
      (fun _ => rfl)).le y hy
    have hb' : -toReal μ * y 0 + y 1 ≤ toReal (S.boundDot
        (c := rowLin (fun _ : Fin 1 => ![neg μ, one]) 0) ![neg μ, one] (fun _ => rfl)).val := by
      have : (rowLin (fun _ : Fin 1 => ![neg μ, one]) 0) y = -toReal μ * y 0 + y 1 := by
        show (Scalar.toRealMat (fun _ : Fin 1 => ![neg μ, one]) *ᵥ y) 0 = _
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Scalar.toRealMat_apply]
        show toReal ((![neg μ, one] : Vec 𝕋 2) 0) * y 0 + toReal ((![neg μ, one] : Vec 𝕋 2) 1) * y 1
          = _
        simp [toReal_neg, toReal_one]
      rw [← this]; exact hb
    have hm := mul_le_mulUp μ γ
    have := add_le_addUp (S.boundDot (c := rowLin (fun _ : Fin 1 => ![neg μ, one]) 0)
      ![neg μ, one] (fun _ => rfl)).val (mulUp μ γ)
    rw [h0] at hb'
    rw [h1] at hb'
    nlinarith [hb', hm, this]
  -- the fold of `minimum` stays above `x·ℓ`
  have hfold : ∀ (l : List (Fin S.h)) (f : Fin S.h → 𝕋) (a : 𝕋),
      x ⬝ᵥ toRealVec ℓ ≤ toReal a → (∀ j, x ⬝ᵥ toRealVec ℓ ≤ toReal (f j)) →
      x ⬝ᵥ toRealVec ℓ ≤ toReal (l.foldl (fun m j => minimum m (f j)) a) := by
    intro l f
    induction l with
    | nil => exact fun a h _ => h
    | cons j l ih =>
      exact fun a h hf => ih _ (by rw [toReal_minimum]; exact le_min h (hf j)) hf
  exact hfold _ _ _ (hdual zero) (fun j => hdual _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
