module

public import CORALean.ContSet.ConZonotope.Real.Operations.Lift
public import CORALean.ContSet.ConZonotope.Real.Operations.MemOfMatIff
public import CORALean.ContSet.ConZonotope.Real.Theorems.MemConstruct

@[expose] public section

/-!
# The lifted zonotope decides membership

[1, Prop. 3]: for the partition `[A b] = [A₁ b₁; A₂ b₂]` and every `z`, `z ∈ Z` iff `[z; 0] ∈ Z⁺`.
`Z` is `ofMat c G A b` and `Z⁺` is `lift`; the partition is the first `m₁` rows against the last
`m₂`. At `m₂ = 0`, `Z⁺` is a zonotope: see `mem_lift_zero_iff`.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3]: `z ∈ {G, c, A, b}` iff `[z; 0] ∈ {[G; A₁], [c; −b₁], A₂, b₂}`. -/
theorem ConZonotope.mem_iff_append_mem_lift {n m₁ m₂ h : ℕ} (c : Vec ℝ n)
    (G : Fin h → Vec ℝ n) (A : Mat ℝ (m₁ + m₂) h) (b : Vec ℝ (m₁ + m₂))
    (z : Vec ℝ n) : -- --- STMT ---
    z ∈ (ConZonotope.ofMat c G A b).construct ↔
      (Fin.append z (0 : Vec ℝ m₁) : Vec ℝ (n + m₁))
        ∈ (ConZonotope.lift (m₂ := m₂) c G A b).construct := by -- --- PROOF ---
  unfold ConZonotope.lift
  rw [ConZonotope.mem_ofMat_iff, ConZonotope.mem_ofMat_iff]
  -- the generators' coefficients enter as `βⱼ · Aᵢⱼ`; `Aβ` writes them `Aᵢⱼ · βⱼ`
  have hcomm : ∀ (β : Vec ℝ h) (r : Fin (m₁ + m₂)),
      ∑ x, β x * A r x = ∑ x, A r x * β x := fun β r =>
    Finset.sum_congr rfl fun x _ => mul_comm _ _
  constructor
  · rintro ⟨β, hβ, hAβ, rfl⟩
    refine ⟨β, hβ, fun i => hAβ (Fin.natAdd m₁ i), funext fun k => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp [Finset.sum_apply]
    · -- the dual rows: `Σ_j A₁ᵢⱼ βⱼ = bᵢ` is row `castAdd i` of `Aβ = b`
      have := hAβ (Fin.castAdd m₂ i)
      simp only [Matrix.mulVec, dotProduct] at this
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply,
        Fin.append_right, Pi.zero_apply]
      simp only [hcomm, this]
      ring
  · rintro ⟨β, hβ, hA2, hx⟩
    refine ⟨β, hβ, fun r => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) r
      · have := congrFun hx (Fin.natAdd n i)
        simp [Finset.sum_apply] at this
        simp only [Matrix.mulVec, dotProduct]
        linarith [hcomm β (Fin.castAdd m₂ i)]
      · exact hA2 i
    · funext i
      have := congrFun hx (Fin.castAdd m₁ i)
      simpa [Finset.sum_apply] using this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
