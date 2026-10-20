module

public import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
public import CORALean.ContSet.HPolytope.Real.Theorems.MemIneqsOfCert
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# Two AH-polytopes within `D` of each other

`[1, Prop. 5]`: a feasible point of the linear program `[1, Prop. 5, Eq. 39]` bounds the Hausdorff
distance of `X₁ = x̄₁ + X₁ P₁` and `X₂ = x̄₂ + X₂ P₂` by `D`, in the norm whose unit ball is
`P_Ball = {H_B x ≤ h_B}`: it is `[1, Prop. 2]` twice, for `X₁ ⊆ X₂ ⊕ D P_Ball` and back
(`[1, Prop. 5, Eq. 40]`), which is what `d_H ≤ D` means. Two indices of the printed program are
misprinted and are read as `[1, Prop. 2]` gives them: `Λ₃ H₄ = H_B Γ₄` is `Λ₄ H₂ = H_B Γ₄`,
and `Λ₃ h₂ ≤ h₂ + H₁ β₃` is `Λ₃ h₂ ≤ h₁ + H₁ β₃`. `ahPolytope_hausdorffDist_le_of_cert`
reads the inclusions as a distance at `P_Ball` the supremum-norm ball.

## Inputs
* `x₁` – point of length `n`
* `x₂` – point of length `n`
* `X₁` – `n × n₁` matrix
* `X₂` – `n × n₂` matrix
* `H₁` – `q₁ × n₁` matrix
* `h₁` – vector of length `q₁`
* `H₂` – `q₂ × n₂` matrix
* `h₂` – vector of length `q₂`
* `HB` – `qB × n` matrix
* `hB` – vector of length `qB`
* `D` – real number
* `Λ₁` – `q₂ × q₁` matrix
* `Λ₂` – `qB × q₁` matrix
* `Λ₃` – `q₁ × q₂` matrix
* `Λ₄` – `qB × q₂` matrix
* `Γ₁` – `n₂ × n₁` matrix
* `Γ₂` – `n × n₁` matrix
* `Γ₃` – `n₁ × n₂` matrix
* `Γ₄` – `n × n₂` matrix
* `β₁` – vector of length `n₂`
* `β₂` – vector of length `n`
* `β₃` – vector of length `n₁`
* `β₄` – vector of length `n`

## Hypotheses
* `hΛ₁` – `Λ₁` has nonnegative entries
* `hΛ₂` – `Λ₂` has nonnegative entries
* `hΛ₃` – `Λ₃` has nonnegative entries
* `hΛ₄` – `Λ₄` has nonnegative entries
* `e₁` – `Λ₁` carries `H₁` to `H₂ Γ₁`
* `e₂` – `Λ₂` carries `H₁` to `HB Γ₂`
* `f₁` – the bound of `Λ₁` is at most `h₂ + H₂ β₁`
* `f₂` – the bound of `Λ₂` is at most `D hB + HB β₂`
* `e₃` – `Λ₃` carries `H₂` to `H₁ Γ₃`
* `e₄` – `Λ₄` carries `H₂` to `HB Γ₄`
* `f₃` – the bound of `Λ₃` is at most `h₁ + H₁ β₃`
* `f₄` – the bound of `Λ₄` is at most `D hB + HB β₄`
* `c₁` – `x₂` is `x₁` shifted by `X₂ β₁ + β₂`
* `g₁` – `X₁` is `X₂ Γ₁ + Γ₂`
* `c₂` – `x₁` is `x₂` shifted by `X₁ β₃ + β₄`
* `g₂` – `X₂` is `X₁ Γ₃ + Γ₄`

## Conclusion
* two AH-polytopes within `D` of each other

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n n₁ n₂ q₁ q₂ qB : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ahPolytope_subset_add_ball_of_cert {x₁ x₂ : Vec ℝ n} {X₁ : Mat ℝ n n₁}
    {X₂ : Mat ℝ n n₂} {H₁ : Mat ℝ q₁ n₁} {h₁ : Vec ℝ q₁} {H₂ : Mat ℝ q₂ n₂} {h₂ : Vec ℝ q₂}
    {HB : Mat ℝ qB n} {hB : Vec ℝ qB} {D : ℝ}
    {Λ₁ : Mat ℝ q₂ q₁} {Λ₂ : Mat ℝ qB q₁} {Λ₃ : Mat ℝ q₁ q₂} {Λ₄ : Mat ℝ qB q₂}
    {Γ₁ : Mat ℝ n₂ n₁} {Γ₂ : Mat ℝ n n₁} {Γ₃ : Mat ℝ n₁ n₂} {Γ₄ : Mat ℝ n n₂}
    {β₁ : Vec ℝ n₂} {β₂ : Vec ℝ n} {β₃ : Vec ℝ n₁} {β₄ : Vec ℝ n}
    (hΛ₁ : ∀ i j, 0 ≤ Λ₁ i j) (hΛ₂ : ∀ i j, 0 ≤ Λ₂ i j) (hΛ₃ : ∀ i j, 0 ≤ Λ₃ i j)
    (hΛ₄ : ∀ i j, 0 ≤ Λ₄ i j)
    (e₁ : Λ₁ * H₁ = H₂ * Γ₁) (e₂ : Λ₂ * H₁ = HB * Γ₂) (f₁ : Λ₁ *ᵥ h₁ ≤ h₂ + H₂ *ᵥ β₁)
    (f₂ : Λ₂ *ᵥ h₁ ≤ D • hB + HB *ᵥ β₂)
    (e₃ : Λ₃ * H₂ = H₁ * Γ₃) (e₄ : Λ₄ * H₂ = HB * Γ₄) (f₃ : Λ₃ *ᵥ h₂ ≤ h₁ + H₁ *ᵥ β₃)
    (f₄ : Λ₄ *ᵥ h₂ ≤ D • hB + HB *ᵥ β₄)
    (c₁ : x₂ - X₂ *ᵥ β₁ - β₂ = x₁) (g₁ : X₂ * Γ₁ + Γ₂ = X₁)
    (c₂ : x₁ - X₁ *ᵥ β₃ - β₄ = x₂) (g₂ : X₁ * Γ₃ + Γ₄ = X₂) : -- --- CONCL ---
    HPolytope.ahPolytope x₁ X₁ (HPolytope.ineqs H₁ h₁)
        ⊆ HPolytope.ahPolytope x₂ X₂ (HPolytope.ineqs H₂ h₂)
          + (HPolytope.ineqs HB (D • hB)).construct ∧
      HPolytope.ahPolytope x₂ X₂ (HPolytope.ineqs H₂ h₂)
        ⊆ HPolytope.ahPolytope x₁ X₁ (HPolytope.ineqs H₁ h₁)
          + (HPolytope.ineqs HB (D • hB)).construct := by -- --- PROOF ---
  -- `x̄ + X p = (x̄' + X' (Γ p - β)) + (Γ' p - β')`, each piece certified
  have key : ∀ {ma mb qa qb : ℕ} {xa xb : Vec ℝ n} {Xa : Mat ℝ n ma} {Xb : Mat ℝ n mb}
      {Ha : Mat ℝ qa ma} {ha : Vec ℝ qa} {Hb : Mat ℝ qb mb} {hb : Vec ℝ qb}
      {Λa : Mat ℝ qb qa} {Λb : Mat ℝ qB qa} {Γa : Mat ℝ mb ma} {Γb : Mat ℝ n ma}
      {βa : Vec ℝ mb} {βb : Vec ℝ n}, (∀ i j, 0 ≤ Λa i j) → (∀ i j, 0 ≤ Λb i j) →
      Λa * Ha = Hb * Γa → Λb * Ha = HB * Γb → Λa *ᵥ ha ≤ hb + Hb *ᵥ βa →
      Λb *ᵥ ha ≤ D • hB + HB *ᵥ βb → xb - Xb *ᵥ βa - βb = xa → Xb * Γa + Γb = Xa →
      HPolytope.ahPolytope xa Xa (HPolytope.ineqs Ha ha)
        ⊆ HPolytope.ahPolytope xb Xb (HPolytope.ineqs Hb hb)
          + (HPolytope.ineqs HB (D • hB)).construct := by
    intro ma mb qa qb xa xb Xa Xb Ha ha Hb hb Λa Λb Γa Γb βa βb hΛa hΛb ea eb fa fb c g
    rintro _ ⟨p, hp, rfl⟩
    refine Set.mem_add.mpr ⟨xb + Xb *ᵥ (Γa *ᵥ p - βa),
      ⟨_, HPolytope.mem_ineqs_of_cert hΛa ea fa hp, rfl⟩, Γb *ᵥ p - βb,
      HPolytope.mem_ineqs_of_cert hΛb eb fb hp, ?_⟩
    rw [← c, ← g, add_mulVec, mulVec_sub, mulVec_mulVec]
    abel
  exact ⟨key hΛ₁ hΛ₂ e₁ e₂ f₁ f₂ c₁ g₁, key hΛ₃ hΛ₄ e₃ e₄ f₃ f₄ c₂ g₂⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
