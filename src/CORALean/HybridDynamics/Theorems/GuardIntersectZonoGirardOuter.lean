import CORALean.HybridDynamics.Theorems.ZonoGirardUpperLe

/-!
# `Location.guardIntersectZonoGirard` holds every state that meets the guard

A state `x` of one of the reach sets on the hyperplane has `x·ℓ` between the lower and upper
cut of that set along every column `ℓ` of a basis, so between the hull's ends. With `B Bᵀ = 1`
the basis carries `x` through its coordinates `Bᵀ x` and back. Outer only: the dual bound is
proved to bound the cut, not to equal it.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A state in a reach set and on the hyperplane lies in the enclosure, for orthogonal bases. -/
theorem Location.guardIntersectZonoGirard_outer (Bs : List (Mat ℝ n n))
    (R₀ : Real.Zonotope (Vec ℝ n)) (Rs : List (Real.Zonotope (Vec ℝ n))) (nv : Vec ℝ n) (γ : ℝ)
    (horth : ∀ B ∈ Bs, B * Bᵀ = 1) {R : Real.Zonotope (Vec ℝ n)} (hR : R ∈ R₀ :: Rs)
    {x : Vec ℝ n} (hx : x ∈ R.construct) (hg : x ⬝ᵥ nv = γ) :
    x ∈ Location.guardIntersectZonoGirard Bs R₀ Rs nv γ := by -- --- PROOF ---
  -- the cut of the set `R` is on both sides of `x·ℓ`
  have hup : ∀ ℓ : Vec ℝ n, x ⬝ᵥ ℓ ≤ Rs.foldl (fun m Z => max m (Location.zonoGirardUpper Z nv γ ℓ))
      (Location.zonoGirardUpper R₀ nv γ ℓ) := fun ℓ => by
    have hfold : ∀ (l : List (Real.Zonotope (Vec ℝ n))) (a : ℝ),
        (x ⬝ᵥ ℓ ≤ a ∨ ∃ Z ∈ l, x ⬝ᵥ ℓ ≤ Location.zonoGirardUpper Z nv γ ℓ) →
        x ⬝ᵥ ℓ ≤ l.foldl (fun m Z => max m (Location.zonoGirardUpper Z nv γ ℓ)) a := by
      -- induction on the list: once the fold passes the state it stays past it
      intro l
      induction l with
      | nil => exact fun a h => h.resolve_right (by simp)
      | cons Z l ih =>
        -- the new accumulator is past the state, or a later set is
        intro a h
        refine ih _ ?_
        rcases h with h | ⟨Z', hZ', h⟩
        · exact Or.inl (le_trans h (le_max_left _ _))
        · rcases List.mem_cons.mp hZ' with rfl | hZ'
          · exact Or.inl (le_trans h (le_max_right _ _))
          · exact Or.inr ⟨Z', hZ', h⟩
    -- the set `R` holding the state is the first or one of the rest
    refine hfold Rs _ ?_
    rcases List.mem_cons.mp hR with rfl | hR'
    · exact Or.inl (Location.zonoGirardUpper_le _ nv γ ℓ hx hg)
    · exact Or.inr ⟨R, hR', Location.zonoGirardUpper_le _ nv γ ℓ hx hg⟩
  -- and the lower end, the upper end in the direction `-ℓ`, negated
  have hlo : ∀ ℓ : Vec ℝ n, Rs.foldl (fun m Z => min m (-Location.zonoGirardUpper Z nv γ (-ℓ)))
      (-Location.zonoGirardUpper R₀ nv γ (-ℓ)) ≤ x ⬝ᵥ ℓ := fun ℓ => by
    have hfold : ∀ (l : List (Real.Zonotope (Vec ℝ n))) (a : ℝ),
        (a ≤ x ⬝ᵥ ℓ ∨ ∃ Z ∈ l, -Location.zonoGirardUpper Z nv γ (-ℓ) ≤ x ⬝ᵥ ℓ) →
        l.foldl (fun m Z => min m (-Location.zonoGirardUpper Z nv γ (-ℓ))) a ≤ x ⬝ᵥ ℓ := by
      -- induction on the list: once the fold passes the state it stays past it
      intro l
      induction l with
      | nil => exact fun a h => h.resolve_right (by simp)
      | cons Z l ih =>
        -- the new accumulator is past the state, or a later set is
        intro a h
        refine ih _ ?_
        rcases h with h | ⟨Z', hZ', h⟩
        · exact Or.inl (le_trans (min_le_left _ _) h)
        · rcases List.mem_cons.mp hZ' with rfl | hZ'
          · exact Or.inl (le_trans (min_le_right _ _) h)
          · exact Or.inr ⟨Z', hZ', h⟩
    have hneg : ∀ Z : Real.Zonotope (Vec ℝ n), x ∈ Z.construct →
        -Location.zonoGirardUpper Z nv γ (-ℓ) ≤ x ⬝ᵥ ℓ := fun Z hZ => by
      have := Location.zonoGirardUpper_le Z nv γ (-ℓ) hZ hg
      rw [dotProduct_neg] at this
      linarith
    -- the set `R` holding the state is the first or one of the rest
    refine hfold Rs _ ?_
    rcases List.mem_cons.mp hR with rfl | hR'
    · exact Or.inl (hneg _ hx)
    · exact Or.inr ⟨R, hR', hneg _ hx⟩
  -- the basis `i` carries `x` to its coordinates and back
  refine Set.mem_iInter.mpr fun i => ⟨Bs[i]ᵀ *ᵥ x, fun k => ?_, ?_⟩
  · have hk : (Bs[i]ᵀ *ᵥ x) k = x ⬝ᵥ (Bs[i]ᵀ k) := by
      rw [Matrix.mulVec, dotProduct_comm]
    rw [hk]
    exact ⟨hlo _, hup _⟩
  · show Bs[i] *ᵥ (Bs[i]ᵀ *ᵥ x) = x
    have hB : Bs[i] * Bs[i]ᵀ = 1 := horth _ (List.getElem_mem _)
    rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
