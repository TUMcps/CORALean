import CORALean.ContSet.Conversion.Real.VPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombExactOfDependent
import CORALean.ContSet.PolyZonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull

/-!
# A hull as a polynomial zonotope

Two readings. `polyZonotope` goes through the hull's own box and that box's
zonotope, then the zonotope's exact reading with one factor per generator:
cheap, and it loses whatever the box route loses and nothing further.

`exists_polyZonotope_exact` is [1, Thm. 1] and loses nothing. A vertex is a
polynomial zonotope with no generators at all; polynomial zonotopes without an
independent block are closed under the convex hull, which is `linComb` and
[1, Prop. 14]; and folding that over the vertex list reaches the hull of them
all. Existence rather than a conversion of its own, as [1] states it: the
counts grow with the vertex list, so the construction is a recursion and no one
type holds its results.

`0 < P.k` is what *bounded polytope* means here, a vertex list of length zero
denoting `∅` where a polynomial zonotope always has a point.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   12-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {n : ℕ}

noncomputable def VPolytope.polyZonotope (P : VPolytope (Vec ℝ n)) : PolyZonotope (Vec ℝ n) :=
  P.zonotope.polyZonotope

theorem VPolytope.polyZonotope_contains (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.polyZonotope.construct :=
  subset_trans P.zonotope_contains (Zonotope.polyZonotope_exact _).subset


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `segments` is Mathlib's convex join: the segment parameter runs over `[0,1]`
either way, one written as `λ` and the other as `1 - λ`. -/
theorem VPolytope.aux_segments_eq_convexJoin (X Y : Set α) :
    segments X Y = convexJoin ℝ X Y := by -- --- PROOF ---
  ext x
  simp only [segments, Set.mem_setOf_eq, mem_convexJoin, segment_eq_image, Set.mem_image,
    Set.mem_Icc]
  constructor
  · rintro ⟨y₁, h₁, y₂, h₂, lam, ⟨hl₀, hl₁⟩, rfl⟩
    exact ⟨y₁, h₁, y₂, h₂, 1 - lam, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩
  · rintro ⟨y₁, h₁, y₂, h₂, θ, ⟨h₀, h₁'⟩, rfl⟩
    exact ⟨y₁, h₁, y₂, h₂, 1 - θ, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩

/-- A point's polynomial zonotope denotes that point and nothing else. -/
theorem VPolytope.aux_ofPoint_construct (v : α) :
    (PolyZonotope.ofPoint v).construct = {v} := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · -- neither generator block has a column, so nothing is added to the centre
    rintro _ ⟨a, β, -, -, rfl⟩
    show (PolyZonotope.ofPoint v).c + ∑ i : Fin 0, PolyZonotope.monomial _ a i • _
        + ∑ j : Fin 0, β j • _ ∈ ({v} : Set α)
    rw [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty, add_zero, add_zero]
    rfl
  · intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact PolyZonotope.mem_ofPoint v

/-- The hull of the first `r + 1` vertices, one `linComb` per vertex added. -/
noncomputable def VPolytope.aux_hullPZ : (r : ℕ) → (V : Fin (r + 1) → α) → PolyZonotope α
  | 0, V => PolyZonotope.ofPoint (V 0)
  | r + 1, V => (VPolytope.aux_hullPZ r fun i => V i.castSucc).linComb
      (PolyZonotope.ofPoint (V (Fin.last (r + 1))))

/-- It never acquires an independent generator, which is the hypothesis
`linComb_exact_of_dependent` runs on. -/
theorem VPolytope.aux_hullPZ_q : ∀ (r : ℕ) (V : Fin (r + 1) → α),
    (VPolytope.aux_hullPZ r V).q = 0 := by -- --- PROOF ---
  intro r
  induction r with
  | zero => intro _; rfl
  | succ k ih =>
    intro V
    -- `linComb` adds the two counts, and a point contributes none
    show (VPolytope.aux_hullPZ k fun i => V i.castSucc).q
        + (PolyZonotope.ofPoint (V (Fin.last (k + 1)))).q = 0
    rw [ih fun i => V i.castSucc]
    rfl

omit [AddCommGroup α] [Module ℝ α] in
/-- The vertex list split at its last entry, which is how the recursion reads
it. -/
theorem VPolytope.aux_range_lastCases {k : ℕ} (V : Fin (k + 1 + 1) → α) :
    Set.range V = insert (V (Fin.last (k + 1)))
      (Set.range fun i : Fin (k + 1) => V i.castSucc) := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨i, rfl⟩
    exact Fin.lastCases (Set.mem_insert _ _) (fun j => Set.mem_insert_of_mem _ ⟨j, rfl⟩) i
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | ⟨j, rfl⟩
    · exact ⟨Fin.last (k + 1), rfl⟩
    · exact ⟨j.castSucc, rfl⟩

/-- What the recursion denotes: the convex hull of the vertices it has read. -/
theorem VPolytope.aux_hullPZ_construct : ∀ (r : ℕ) (V : Fin (r + 1) → α),
    (VPolytope.aux_hullPZ r V).construct = convexHull ℝ (Set.range V) := by -- --- PROOF ---
  intro r
  induction r with
  | zero =>
    intro V
    -- one vertex, and a hull of one point is that point
    have hrange : Set.range V = {V 0} := by
      apply Set.eq_of_subset_of_subset
      · rintro _ ⟨i, rfl⟩
        exact Fin.cases (Set.mem_singleton _) (fun j => j.elim0) i
      · intro x hx
        exact ⟨0, (Set.mem_singleton_iff.mp hx).symm⟩
    rw [show VPolytope.aux_hullPZ 0 V = PolyZonotope.ofPoint (V 0) from rfl,
      VPolytope.aux_ofPoint_construct, hrange, convexHull_singleton]
  | succ k ih =>
    intro V
    have hq : (VPolytope.aux_hullPZ k fun i => V i.castSucc).q = 0 :=
      VPolytope.aux_hullPZ_q k _
    show ((VPolytope.aux_hullPZ k fun i => V i.castSucc).linComb
        (PolyZonotope.ofPoint (V (Fin.last (k + 1))))).construct = _
    -- the hull of one more vertex is a segment away from the hull so far
    rw [← PolyZonotope.linComb_exact_of_dependent _ _ hq rfl, ih fun i => V i.castSucc,
      VPolytope.aux_ofPoint_construct, VPolytope.aux_segments_eq_convexJoin,
      convexJoin_comm, ← convexHull_insert (Set.range_nonempty _),
      ← VPolytope.aux_range_lastCases V]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: a bounded polytope is a polynomial zonotope exactly, not merely
within one. -/
theorem VPolytope.exists_polyZonotope_exact (P : VPolytope α) (hk : 0 < P.k) :
    ∃ pZ : PolyZonotope α, pZ.construct = P.construct := by -- --- PROOF ---
  obtain ⟨k, V⟩ := P
  -- the recursion reads a non-empty list, which is what `hk` supplies
  have hk' : 0 < k := hk
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  refine ⟨VPolytope.aux_hullPZ r V, ?_⟩
  rw [VPolytope.construct_eq_convexHull (⟨r + 1, V⟩ : VPolytope α)]
  exact VPolytope.aux_hullPZ_construct r V

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
