module

public import CORALean.HybridDynamics.Operations.CheckFlowFloat
public import CORALean.HybridDynamics.Theorems.InputSetFloatOuter
public import CORALean.ContSet.ContSet.Theorems.ProjectOnHyperplaneFloatOuter
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_HPolytope

@[expose] public section

/-!
# A reach set `Location.checkFlowFloat` drops has no outward flow on its projection

A dropped set was certified `le flowUp zero`, so the rounded-up support function of the flow set
`A·proj ⊞ V`, `V = inputSetFloat`, along `c` is `≤ 0`. The projection of a state of the set is a
point of the float projection (`projectOnHyperplaneFloat_outer`), its image under `A` plus a
combined input `B u + c₀ + E w` is a point of the flow set (`inputSetFloat_outer`), and `c` of it
is under the support bound. A statement about the projection, not
about the set itself.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps CORALean.Float.SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {G : ℕ → Type}
  [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, ContSet (G n) (Vec ℝ n)] in
/-- A dropped set carries the flow nowhere outward on its projection. -/
theorem Location.checkFlowFloat_dropped
    (ℓ : Location 𝒵[𝕋] G L 𝕋 n) (c : Vec 𝕋 n)
    (d : 𝕋) (Rs : List (Zonotope (Vec 𝕋 n))) {R : Zonotope (Vec 𝕋 n)} (hR : R ∈ Rs)
    (hdrop : R ∉ ℓ.checkFlowFloat c d Rs) {x : Vec ℝ n} {u : Vec ℝ ℓ.dynamics.m}
    {w : Vec ℝ ℓ.dynamics.r} (hx : x ∈ R.construct) (hu : u ∈ ContSet.construct ℓ.U)
    (hw : w ∈ ContSet.construct ℓ.W) : -- --- STMT ---
    toRealVec c ⬝ᵥ (Scalar.toRealMat ℓ.dynamics.A *ᵥ
      (x - (toRealVec c ⬝ᵥ x - toReal d) • toRealVec c) + (Scalar.toRealMat ℓ.dynamics.B *ᵥ u +
        toRealVec ℓ.dynamics.c + Scalar.toRealMat ℓ.dynamics.E *ᵥ w)) ≤ 0 := by -- --- PROOF ---
  -- dropped means the second test certified `flowUp ≤ 0`
  have hle : le (((Plus.plus
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) ℓ.dynamics.A
      (ContSet.projectOnHyperplaneFloat (S := 𝒵[𝕋]) R c d)) ℓ.inputSetFloat).boundDot
        (c := rowLin (fun _ : Fin 1 => c) 0) c fun _ => rfl).val) zero = true := by
    by_contra hne
    refine hdrop (List.mem_filter.mpr ⟨hR, ?_⟩)
    simp only [Bool.or_eq_true, Bool.not_eq_true']
    exact Or.inr (by simpa using hne)
  -- the projected state, a flow input and the flow set
  have hp := ContSet.projectOnHyperplaneFloat_outer (S := 𝒵[𝕋]) R c
    d ⟨x, hx, rfl⟩
  have hmap := Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) ℓ.dynamics.A
    (ContSet.projectOnHyperplaneFloat (S := 𝒵[𝕋]) R c d)
      (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hp))
  have hflow := Plus.plus_outer
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) ℓ.dynamics.A
      (ContSet.projectOnHyperplaneFloat (S := 𝒵[𝕋]) R c d)) ℓ.inputSetFloat
    ⟨_, hmap, _, ℓ.inputSetFloat_outer hu hw, rfl⟩
  have hb := (((Plus.plus (Mtimes.mtimes (𝕄 := Mat 𝕋)
    (S := 𝒵[𝕋]) ℓ.dynamics.A
      (ContSet.projectOnHyperplaneFloat (S := 𝒵[𝕋]) R c d)) ℓ.inputSetFloat).boundDot
        (c := rowLin (fun _ : Fin 1 => c) 0) c fun _ => rfl)).le _ hflow
  have h0 := toReal_le_of_le hle
  rw [toReal_zero] at h0
  exact le_trans hb h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
