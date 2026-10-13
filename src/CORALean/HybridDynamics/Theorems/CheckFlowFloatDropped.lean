module

public import CORALean.HybridDynamics.Operations.CheckFlowFloat
public import CORALean.ContSet.ContSet.Theorems.ProjectOnHyperplaneFloatOuter

@[expose] public section

/-!
# A reach set `Location.checkFlowFloat` drops has no outward flow on its projection

A dropped set was certified `le flowUp zero`, so the rounded-up support function of the flow set
`A·proj ⊞ U` along `c` is `≤ 0`. The projection of a state of the set is a point of the float
projection (`projectOnHyperplaneFloat_outer`), its image under `A` plus an input is a point of
the flow set, and `c` of it is under the support bound. A statement about the projection, not
about the set itself.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
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
    (ℓ : Location (fun k => Zonotope (Vec 𝕋 k)) G L 𝕋 n) (c : Vec 𝕋 n)
    (d : 𝕋) (Rs : List (Zonotope (Vec 𝕋 n))) {R : Zonotope (Vec 𝕋 n)} (hR : R ∈ Rs)
    (hdrop : R ∉ ℓ.checkFlowFloat c d Rs) {x u : Vec ℝ n} (hx : x ∈ R.construct)
    (hu : u ∈ ContSet.construct ℓ.U) :
    toRealVec c ⬝ᵥ (Scalar.toRealMat ℓ.dynamics.A *ᵥ
      (x - (toRealVec c ⬝ᵥ x - toReal d) • toRealVec c) + u) ≤ 0 := by -- --- PROOF ---
  -- dropped means the second test certified `flowUp ≤ 0`
  have hle : le (((Plus.plus
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) ℓ.dynamics.A
      (ContSet.projectOnHyperplaneFloat (S := fun k => Zonotope (Vec 𝕋 k)) R c d)) ℓ.U).boundDot
        (c := rowLin (fun _ : Fin 1 => c) 0) c fun _ => rfl).val) zero = true := by
    by_contra hne
    refine hdrop (List.mem_filter.mpr ⟨hR, ?_⟩)
    simp only [Bool.or_eq_true, Bool.not_eq_true']
    exact Or.inr (by simpa using hne)
  -- the projected state, a flow input and the flow set
  have hp := ContSet.projectOnHyperplaneFloat_outer (S := fun k => Zonotope (Vec 𝕋 k)) R c
    d ⟨x, hx, rfl⟩
  have hmap := Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) ℓ.dynamics.A
    (ContSet.projectOnHyperplaneFloat (S := fun k => Zonotope (Vec 𝕋 k)) R c d)
      (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hp))
  have hflow := Plus.plus_outer
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) ℓ.dynamics.A
      (ContSet.projectOnHyperplaneFloat (S := fun k => Zonotope (Vec 𝕋 k)) R c d)) ℓ.U
    ⟨_, hmap, u, hu, rfl⟩
  have hb := (((Plus.plus (Mtimes.mtimes (𝕄 := Mat 𝕋)
    (S := fun k => Zonotope (Vec 𝕋 k)) ℓ.dynamics.A
      (ContSet.projectOnHyperplaneFloat (S := fun k => Zonotope (Vec 𝕋 k)) R c d)) ℓ.U).boundDot
        (c := rowLin (fun _ : Fin 1 => c) 0) c fun _ => rfl)).le _ hflow
  have h0 := toReal_le_of_le hle
  rw [toReal_zero] at h0
  exact le_trans hb h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
