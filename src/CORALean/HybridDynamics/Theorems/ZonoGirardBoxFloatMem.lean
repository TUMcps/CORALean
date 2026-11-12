module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.HybridDynamics.Operations.ZonoGirardBoxFloat
public import CORALean.HybridDynamics.Theorems.ZonoGirardUpperFloatLe
public import CORALean.ContSet.Interval.Float.Theorems.OrOuter

@[expose] public section

/-!
# `Location.zonoGirardBoxFloat` holds the coordinates of every state that meets the guard

A state `x` of a reach set on the hyperplane has `x·ℓ` between the ends of that set's cut along
each column `ℓ` of `B` (`zonoGirardUpperFloat_le` in the directions `ℓ` and `-ℓ`), so its
coordinates `Bᵀ x` lie in the joined interval. No orthogonality is needed here.

## Inputs
* `B` – basis
* `R₀` – initial set
* `Rs` – reach sets
* `nv` – guard normal
* `γ` – guard offset
* `R` – reach set
* `x` – state

## Hypotheses
* `hR` – the reach set is among the given ones
* `hx` – state lies in the reach set
* `hg` – state lies on the guard

## Conclusion
* the coordinates of the state lie in the box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps CORALean.Float.SoundFloatArithmetic Matrix
  ContSet ContSetLike

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The coordinates `Bᵀ x` of a state of a reach set on the hyperplane lie in the joined cuts. -/
theorem Location.zonoGirardBoxFloat_mem (B : Mat 𝕋 n n) (R₀ : Zonotope (Vec 𝕋 n))
    (Rs : List (Zonotope (Vec 𝕋 n))) (nv : Vec 𝕋 n) (γ : 𝕋)
    {R : Zonotope (Vec 𝕋 n)} (hR : R ∈ R₀ :: Rs) {x : Vec ℝ n} (hx : x ∈ R.toSet)
    (hg : x ⬝ᵥ toRealVec nv = toReal γ) : -- --- CONCL ---
    Scalar.toRealMat Bᵀ *ᵥ x ∈
      (Location.zonoGirardBoxFloat B R₀ Rs nv γ).toSet := by -- --- PROOF ---
  have hfold : ∀ (Is : List (Interval (Vec 𝕋 n))) (J : Interval (Vec 𝕋 n)) (y : Vec ℝ n),
      (y ∈ J.toSet ∨ ∃ I ∈ Is, y ∈ I.toSet) → y ∈ (Is.foldl Interval.or J).toSet := by
    intro Is
    induction Is with
    | nil => exact fun J y h => h.resolve_right (by simp)
    | cons I Is ih =>
      intro J y h
      rw [List.foldl_cons]
      refine ih _ y ?_
      rcases h with hJ | ⟨I', hI', hy⟩
      · exact Or.inl (Interval.or_outer J I (Or.inl hJ))
      · rcases List.mem_cons.mp hI' with rfl | hI'
        · exact Or.inl (Interval.or_outer J I' (Or.inr hy))
        · exact Or.inr ⟨I', hI', hy⟩
  unfold Location.zonoGirardBoxFloat
  -- the box around the cut of `R'`, from the Girard bounds along the basis
  set boxOf : Zonotope (Vec 𝕋 n) → Interval (Vec 𝕋 n) := fun R' =>
    ⟨fun k => neg (Location.zonoGirardUpperFloat R' nv γ (-(Bᵀ k))),
      fun k => Location.zonoGirardUpperFloat R' nv γ (Bᵀ k)⟩ with hboxOf
  -- the state's coordinates lie in the cut of a set holding it
  have hcut : ∀ R' : Zonotope (Vec 𝕋 n), x ∈ R'.toSet →
      Scalar.toRealMat Bᵀ *ᵥ x ∈ (boxOf R').toSet :=
    fun R' hx' => by
    -- the coordinate `k` of `Bᵀ x` is `x·ℓ` for the column `ℓ` of `B`
    intro k
    have hk : (Scalar.toRealMat Bᵀ *ᵥ x) k = x ⬝ᵥ toRealVec (Bᵀ k) := by
      rw [Matrix.mulVec, dotProduct_comm]
      rfl
    have hu := Location.zonoGirardUpperFloat_le R' nv γ (Bᵀ k) hx' hg
    have hl := Location.zonoGirardUpperFloat_le R' nv γ (-(Bᵀ k)) hx' hg
    have hneg : toRealVec (-(Bᵀ k)) = -toRealVec (Bᵀ k) := toRealVec_neg _
    -- the lower end is the upper end of `-ℓ`, negated
    rw [hneg, dotProduct_neg] at hl
    refine ⟨?_, ?_⟩
    · -- the lower end
      show toReal (neg (Location.zonoGirardUpperFloat R' nv γ (-(Bᵀ k)))) ≤
        (Scalar.toRealMat Bᵀ *ᵥ x) k
      rw [toReal_neg, hk]
      linarith
    · -- the upper end
      show (Scalar.toRealMat Bᵀ *ᵥ x) k ≤ toReal (Location.zonoGirardUpperFloat R' nv γ (Bᵀ k))
      rw [hk]
      exact hu
  -- the state is in the joined interval
  have h2 := hfold (Rs.map fun R' => (boxOf R'))
    ⟨fun k => neg (Location.zonoGirardUpperFloat R₀ nv γ (-(Bᵀ k))),
        fun k => Location.zonoGirardUpperFloat R₀ nv γ (Bᵀ k)⟩
    (Scalar.toRealMat Bᵀ *ᵥ x) (by
      rcases List.mem_cons.mp hR with rfl | hR'
      · exact Or.inl (hcut _ hx)
      · exact Or.inr ⟨_, List.mem_map.mpr ⟨R, hR', rfl⟩, hcut _ hx⟩)
  exact h2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
