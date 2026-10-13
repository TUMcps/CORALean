module

public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Real.Operations.Mspb
public import CORALean.ContSet.Zonotope.Real.Theorems.Cloud2zonotopeMem
public import CORALean.ContSet.Zonotope.Real.Theorems.ConstructSubsetOfSignedSums
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# `Zonotope.mspb` contains every solution domain

[1, Alg. 5, Prop. 7.1 for the trajectory fusion]: each `A [r] + [v]` of the list lies in the
zonotope `Zonotope.mspb` returns. As a zonotope `A [r] + [v]` is `A □[r] ⊕ □[v]` ([1, Prop. 4.2])
whose corners are exactly the potential vertices `A [r]± + [v]±` of `P` ([1, Remark 3]);
`cloud2zonotope` encloses `P` for every ratio, so the one kept does, and a convex set holding the
corners holds the zonotope ([1, Thm. 4]).

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A corner of a box's zonotope is the box's corner. -/
theorem Zonotope.aux_corner_interval_zonotope (I : Interval (Vec ℝ n)) (τ : Fin n → Bool) :
    I.zonotope.corner τ = fun i => if τ i then I.sup i else I.inf i := by -- --- PROOF ---
  funext i
  simp only [Zonotope.corner, Interval.zonotope, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · cases τ i <;> simp <;> ring
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- The corners of `(A □[r]) ⊕ □[v]` are the potential vertices `A [r]± + [v]±`. -/
theorem Zonotope.aux_corner_plus_map (A : Mat ℝ n n) (R V : Interval (Vec ℝ n))
    (σ : Fin (n + n) → Bool) :
    ((R.zonotope.map (Matrix.mulVecLin A)).plus V.zonotope).corner σ =
      A *ᵥ (fun i => if σ (Fin.castAdd n i) then R.sup i else R.inf i) +
        fun i => if σ (Fin.natAdd n i) then V.sup i else V.inf i := by -- --- PROOF ---
  -- the corners of the two boxes' zonotopes, and the corner of a sum is the sum of the corners
  have hR := Zonotope.aux_corner_interval_zonotope R (fun i => σ (Fin.castAdd n i))
  have hV := Zonotope.aux_corner_interval_zonotope V (fun i => σ (Fin.natAdd n i))
  rw [← hR, ← hV]
  have hsum : ∀ f : Fin (n + n) → Vec ℝ n,
      ∑ x, f x = ∑ i : Fin n, f (Fin.castAdd n i) + ∑ i : Fin n, f (Fin.natAdd n i) :=
    fun f => Fin.sum_univ_add f
  -- split the sum over the `n + n` generators in the two halves
  simp only [Zonotope.corner, Zonotope.plus, Zonotope.map]
  erw [hsum]
  have h1 : ∀ x : Fin n, Fin.append (fun j => A *ᵥ R.zonotope.G j) V.zonotope.G
      (Fin.castAdd n x) = A *ᵥ R.zonotope.G x := fun x => Fin.append_left _ _ x
  have h2 : ∀ x : Fin n, Fin.append (fun j => A *ᵥ R.zonotope.G j) V.zonotope.G
      (Fin.natAdd n x) = V.zonotope.G x := fun x => Fin.append_right _ _ x
  have e1 : ∀ c : Fin n → ℝ, ∑ x, c x • Fin.append (fun j => A *ᵥ R.zonotope.G j) V.zonotope.G
      (Fin.castAdd n x) = ∑ x, c x • (A *ᵥ R.zonotope.G x) :=
    fun c => Finset.sum_congr rfl fun x _ => by rw [h1 x]
  have e2 : ∀ c : Fin n → ℝ, ∑ x, c x • Fin.append (fun j => A *ᵥ R.zonotope.G j) V.zonotope.G
      (Fin.natAdd n x) = ∑ x, c x • V.zonotope.G x :=
    fun c => Finset.sum_congr rfl fun x _ => by rw [h2 x]
  erw [e1 (fun x => if σ (Fin.castAdd n x) then (1 : ℝ) else -1),
    e2 (fun x => if σ (Fin.natAdd n x) then (1 : ℝ) else -1)]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul]
  first | rfl | abel


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mspb_outer [NeZero m]
    (dir : (Fin m × (Fin n → Bool) × (Fin n → Bool) → Vec ℝ n) → Vec ℝ n)
    (L : Fin m → Mat ℝ n n × Interval (Vec ℝ n) × Interval (Vec ℝ n)) (l : Fin m)
    {r v : Vec ℝ n} (hr : r ∈ (L l).2.1.construct) (hv : v ∈ (L l).2.2.construct) :
    (L l).1 *ᵥ r + v ∈ (Zonotope.mspb dir L).construct := by -- --- PROOF ---
  -- the points enclosed, and that every candidate kept along the way encloses them
  set XP : Fin m × (Fin n → Bool) × (Fin n → Bool) → Vec ℝ n := fun (l, b, b') =>
    (L l).1 *ᵥ (fun i => if b i then (L l).2.1.sup i else (L l).2.1.inf i) +
      fun i => if b' i then (L l).2.2.sup i else (L l).2.2.inf i with hXP
  have fold : ∀ (is : List ℕ) (M₀ : Zonotope (Vec ℝ n)), (∀ idx, XP idx ∈ M₀.construct) →
      ∀ idx, XP idx ∈ (is.foldl (fun M (k : ℕ) =>
        if (Zonotope.cloud2zonotope dir ((k : ℝ) / 10) n 0 XP).volume < M.volume then
          Zonotope.cloud2zonotope dir ((k : ℝ) / 10) n 0 XP else M) M₀).construct := by
    intro is
    induction is with
    | nil => intro M₀ h; exact h
    | cons k is ih =>
      intro M₀ h
      rw [List.foldl_cons]
      split_ifs
      · exact ih _ (fun idx => Zonotope.cloud2zonotope_mem dir _ n 0 XP idx)
      · exact ih _ h
  -- the result holds every point of `P`: it is one of the candidates
  have hall : ∀ idx, XP idx ∈ (Zonotope.mspb dir L).construct :=
    fold _ _ (fun idx => Zonotope.cloud2zonotope_mem dir 0 n 0 XP idx)
  -- the zonotope of each solution domain has the points of `P` as its corners
  have hcorner : ∀ (l : Fin m) σ, ((((L l).2.1.zonotope.map (Matrix.mulVecLin (L l).1)).plus
      (L l).2.2.zonotope)).corner σ ∈ (Zonotope.mspb dir L).construct := fun l σ => by
    rw [Zonotope.aux_corner_plus_map]
    exact hall (l, fun i => σ (Fin.castAdd n i), fun i => σ (Fin.natAdd n i))
  -- and, being convex, the zonotopes (Thm. 4); then the domain `A [r] + [v]` is one of them
  have hsub := Zonotope.iUnion_construct_subset_of_signedSums_subset
    (fun l => ((L l).2.1.zonotope.map (Matrix.mulVecLin (L l).1)).plus (L l).2.2.zonotope)
    (Zonotope.convex_construct (Zonotope.mspb dir L)) (by
      rintro x hx
      obtain ⟨l, y, ⟨σ, rfl⟩, rfl⟩ := Set.mem_iUnion.mp hx
      exact hcorner l σ)
  refine hsub (Set.mem_iUnion.mpr ⟨l, ?_⟩)
  show _ ∈ (((L l).2.1.zonotope.map (Matrix.mulVecLin (L l).1)).plus (L l).2.2.zonotope).construct
  rw [← Zonotope.plus_exact]
  exact ⟨(L l).1 *ᵥ r,
    (Zonotope.map_exact (Matrix.mulVecLin (L l).1) _) ▸
      ⟨r, Interval.zonotope_contains _ hr, rfl⟩, v, Interval.zonotope_contains _ hv, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
