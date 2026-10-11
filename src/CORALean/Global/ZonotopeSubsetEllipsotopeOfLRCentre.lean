import CORALean.Global.ZonotopeSubsetEllipsotopeOfLR
import Mathlib.Data.Fin.SuccPred

/-!
# The linear relaxation at a shifted centre

[1, Eq. 53]: a zonotope `Z(G, c)` lies in the ellipsotope `E_q(H, d)` if some `X` has
`H X = [G, c - d]` and `‖X‖_{L⊤₁,q} ≤ 1`. It is `[1, Thm. 15 (relaxation)]` at
`G' = [G, c - d]` together with [1, Lemma 14]'s observation that `c + G α = d + G' (α, 1)`, the
coefficient `(α, 1)` being in the unit box. The paper applies it to the reachable set of a
sampled-data system and the terminal region `T`.

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal

variable {m l : ℕ} {W : Type} [AddCommGroup W] [Module ℝ W]


-- =======================================  MAIN THEOREM  ======================================= --

theorem zonotope_subset_ellipsotope_of_lr_centre (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (G : (Fin m → ℝ) →ₗ[ℝ] W) (c d : W) (H : PiLp q (fun _ : Fin l => ℝ) →ₗ[ℝ] W)
    (X : Matrix (Fin l) (Fin (m + 1)) ℝ)
    (hGX : ∀ α' : Fin (m + 1) → ℝ, G (fun i => α' i.castSucc) + α' (Fin.last m) • (c - d) =
      H (WithLp.toLp q (X.mulVec α')))
    (hX : ‖WithLp.toLp q (fun i => ∑ j, |X i j|)‖ ≤ 1) :
    {x | ∃ α : Fin m → ℝ, ‖α‖ ≤ 1 ∧ x = c + G α} ⊆
      {x | ∃ β : PiLp q (fun _ : Fin l => ℝ), ‖β‖ ≤ 1 ∧ x = d + H β} := by -- --- PROOF ---
  rintro _ ⟨α, hα, rfl⟩
  -- the extended coefficients `(α, 1)` are in the unit box, and reach `c + G α - d`
  have hbox : ‖(Fin.snoc α 1 : Fin (m + 1) → ℝ)‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one] at hα ⊢
    intro i
    refine Fin.lastCases (by simp) (fun i => ?_) i
    simpa using hα i
  -- the linear map `G'` with columns `[G, c - d]`
  let G' : (Fin (m + 1) → ℝ) →ₗ[ℝ] W :=
    G ∘ₗ LinearMap.funLeft ℝ ℝ Fin.castSucc +
      (LinearMap.proj (Fin.last m) : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ).smulRight (c - d)
  have hG'X : ∀ α', G' α' = H (WithLp.toLp q (X.mulVec α')) := fun α' => hGX α'
  obtain ⟨β, hβ, hβe⟩ := zonotope_subset_ellipsotope_of_lr q G' H X hG'X hX
    ⟨Fin.snoc α 1, hbox, rfl⟩
  refine ⟨β, hβ, ?_⟩
  -- `c + G α = d + G' (α, 1)`
  have : G' (Fin.snoc α 1) = G α + (c - d) := by simp [G', LinearMap.funLeft]
  rw [← hβe, this]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
