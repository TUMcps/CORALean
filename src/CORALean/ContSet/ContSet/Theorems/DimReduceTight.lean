module

public import CORALean.ContSet.ContSet.Definitions.DimReduce
public import CORALean.ContSet.ContSet.Definitions.IsBoundIntersect2D
public import CORALean.ContSet.ContSet.Theorems.DimReduceOuter
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Dimension reduction is tight in the directions it is given

[1, Alg. 2] claims a polytope that approximates `Z ∩ G` tightly in the directions of `D`. Here
that is: for every `ℓ ∈ D`, `[m_ℓ, M_ℓ]` is the exact range of `x·ℓ` over `Z ∩ G` when
the intersection is nonempty, and the polyhedron attains both ends, `M_ℓ` and `m_ℓ` being its
greatest and least `x·ℓ`. It follows from [1, Prop. 1] and the specification of the routine.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: for `ℓ ∈ D` the polyhedron's `x·ℓ` ranges over exactly `Z ∩ G`'s. -/
theorem ContSet.dimReduce_tight {bound : Set (ℝ × ℝ) → ℝ → Real.Interval ℝ}
    (hb : ContSet.IsBoundIntersect2D bound) (Z : Set (Vec ℝ n)) (nv : Vec ℝ n) (γ : ℝ)
    (D : Finset (Vec ℝ n)) (hne : ∃ x ∈ Z, x ⬝ᵥ nv = γ) {ℓ : Vec ℝ n} (hℓ : ℓ ∈ D) : -- --- STMT ---
    IsGreatest ((fun x => x ⬝ᵥ ℓ) '' ContSet.dimReduce bound Z nv γ D)
        (bound ((fun x : Vec ℝ n => (x ⬝ᵥ nv, x ⬝ᵥ ℓ)) '' Z) γ).sup
      ∧ IsLeast ((fun x => x ⬝ᵥ ℓ) '' ContSet.dimReduce bound Z nv γ D)
        (bound ((fun x : Vec ℝ n => (x ⬝ᵥ nv, x ⬝ᵥ ℓ)) '' Z) γ).inf := by -- --- PROOF ---
  set S := (fun x : Vec ℝ n => (x ⬝ᵥ nv, x ⬝ᵥ ℓ)) '' Z with hS
  -- the segment is nonempty, so both its ends are in the slice, hence reached by `Z ∩ G`
  obtain ⟨x₀, hx₀, hxn₀⟩ := hne
  have hmem : x₀ ⬝ᵥ ℓ ∈ {y : ℝ | (γ, y) ∈ S} := ⟨x₀, hx₀, by simp [hxn₀]⟩
  rw [hb] at hmem
  have hMe : (bound S γ).sup ∈ {y : ℝ | (γ, y) ∈ S} := by
    rw [hb]; exact ⟨hmem.1.trans hmem.2, le_rfl⟩
  have hme : (bound S γ).inf ∈ {y : ℝ | (γ, y) ∈ S} := by
    rw [hb]; exact ⟨le_rfl, hmem.1.trans hmem.2⟩
  obtain ⟨xM, hxM, hxMn⟩ := hMe
  obtain ⟨xm, hxm, hxmn⟩ := hme
  simp only [Prod.mk.injEq] at hxMn hxmn
  have hxM' := ContSet.dimReduce_outer hb Z nv γ D ⟨hxM, hxMn.1⟩
  have hxm' := ContSet.dimReduce_outer hb Z nv γ D ⟨hxm, hxmn.1⟩
  refine ⟨⟨⟨xM, hxM', hxMn.2⟩, ?_⟩, ⟨⟨xm, hxm', hxmn.2⟩, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hx ℓ hℓ).2
  · rintro _ ⟨x, hx, rfl⟩
    exact (hx ℓ hℓ).1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
