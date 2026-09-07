import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGroup
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti

/-!
# A group merge is not always tighter than the pairwise merges it replaces

`relaxWidthGroup_le_chain` weighs widths, and here is why that is all it weighs:
a set where merging two generators pairwise and then onto the target encloses
strictly less than merging them as a group.

The witness is as small as one gets. Two generators share an exponent column
and cancel, `1` and `-1`. The pairwise route merges those two first, at width
`0`, and what it carries to the target is their sum, the zero generator, on
which any width pays nothing. The group route never forms that sum: it pays
width `2` on each of the two separately, and its independent part is `[-4, 4]`
where the pairwise one is `{0}`.

So neither route dominates the other. A group merge saves per member, and a
chain can still be the sharper of the two by merging members into each other
before it pays anything on them.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Two generators at exponent `1` that cancel, and a target at exponent `0`. -/
def aux_notTighter_pZ : PolyZonotope ℝ where
  p := 1
  h := 3
  q := 0
  c := 0
  G := ![0, 1, -1]
  E := ![![0, 1, 1]]
  GI := Fin.elim0

/-- The two on the right, the target kept on the left. -/
def aux_notTighter_part : Split (Fin 3) into (Fin 1) ⊕ (Fin 2) := Partition.split 1 2

/-- The second pairwise step: the merged generator onto the target. A merge
leaves the merged generator last, so this step reads the two the other way
round, which is what the swap is for. -/
def aux_notTighter_part₂ : Split (Fin 2) into (Fin 0) ⊕ (Fin 2) :=
  (Partition.split 0 2).reindex (Equiv.swap 0 1)

/-- The group merge of the two. -/
def aux_notTighter_group : PolyZonotope ℝ :=
  aux_notTighter_pZ.relaxExpGroup aux_notTighter_part 0

/-- The same two merged pairwise, and the result then merged onto the target. -/
def aux_notTighter_chain : PolyZonotope ℝ :=
  (aux_notTighter_pZ.relaxExpMulti aux_notTighter_part).relaxExpMulti aux_notTighter_part₂

-- the two group members sit at exponent `1` and the target at `0`, so each pays `2`
theorem aux_notTighter_width (l : Fin 2) :
    aux_notTighter_pZ.relaxWidthGroup aux_notTighter_part 0 l = 2 := by
  show ∑ i : Fin 1, PolyZonotope.eDiff (aux_notTighter_pZ.E i (aux_notTighter_part.right l))
      (aux_notTighter_pZ.E i (aux_notTighter_part.left 0)) = 2
  rw [Fin.sum_univ_one]
  fin_cases l <;> rfl

theorem aux_notTighter_groupG : aux_notTighter_group.G (0 : Fin 1) = 0 := by -- --- PROOF ---
  show aux_notTighter_pZ.G (aux_notTighter_part.left 0)
      + (if (0 : Fin 1) = 0 then ∑ j, aux_notTighter_pZ.G (aux_notTighter_part.right j) else 0) = 0
  rw [if_pos rfl, Fin.sum_univ_two]
  show (0 : ℝ) + (1 + -1) = 0
  norm_num

theorem aux_notTighter_groupGI0 : aux_notTighter_group.GI (0 : Fin 2) = 2 := by -- --- PROOF ---
  show ((aux_notTighter_pZ.relaxWidthGroup aux_notTighter_part 0 0 : ℕ) : ℝ)
      • aux_notTighter_pZ.G (aux_notTighter_part.right 0) = 2
  rw [aux_notTighter_width]
  show ((2 : ℕ) : ℝ) * (1 : ℝ) = 2
  norm_num

theorem aux_notTighter_groupGI1 : aux_notTighter_group.GI (1 : Fin 2) = -2 := by -- --- PROOF ---
  show ((aux_notTighter_pZ.relaxWidthGroup aux_notTighter_part 0 1 : ℕ) : ℝ)
      • aux_notTighter_pZ.G (aux_notTighter_part.right 1) = -2
  rw [aux_notTighter_width]
  show ((2 : ℕ) : ℝ) * (-1 : ℝ) = -2
  norm_num

/-- What the first pairwise step leaves for the second to carry: the zero
generator, on which the second step's width buys nothing. -/
theorem aux_notTighter_mergedG :
    (aux_notTighter_pZ.relaxExpMulti aux_notTighter_part).G
      (aux_notTighter_part₂.right 0) = 0 := by
  show aux_notTighter_pZ.G (aux_notTighter_part.right 1)
      + aux_notTighter_pZ.G (aux_notTighter_part.right 0) = 0
  show (-1 : ℝ) + 1 = 0
  norm_num

theorem aux_notTighter_chainG : aux_notTighter_chain.G (0 : Fin 1) = 0 := by -- --- PROOF ---
  show (aux_notTighter_pZ.relaxExpMulti aux_notTighter_part).G (aux_notTighter_part₂.right 1)
      + (aux_notTighter_pZ.relaxExpMulti aux_notTighter_part).G (aux_notTighter_part₂.right 0) = 0
  rw [aux_notTighter_mergedG]
  show (0 : ℝ) + 0 = 0
  norm_num

theorem aux_notTighter_chainGI0 : aux_notTighter_chain.GI (0 : Fin 2) = 0 := by -- --- PROOF ---
  show ((aux_notTighter_pZ.relaxWidthMulti aux_notTighter_part : ℕ) : ℝ)
      • aux_notTighter_pZ.G (aux_notTighter_part.right 0) = 0
  -- the two share their exponent column, so the first step merges them for free
  have hw : aux_notTighter_pZ.relaxWidthMulti aux_notTighter_part = 0 := by
    show ∑ i : Fin 1, PolyZonotope.eDiff (aux_notTighter_pZ.E i (aux_notTighter_part.right 0))
        (aux_notTighter_pZ.E i (aux_notTighter_part.right 1)) = 0
    rw [Fin.sum_univ_one]
    rfl
  rw [hw]
  norm_num

theorem aux_notTighter_chainGI1 : aux_notTighter_chain.GI (1 : Fin 2) = 0 := by -- --- PROOF ---
  show (((aux_notTighter_pZ.relaxExpMulti aux_notTighter_part).relaxWidthMulti
      aux_notTighter_part₂ : ℕ) : ℝ)
      • (aux_notTighter_pZ.relaxExpMulti aux_notTighter_part).G
        (aux_notTighter_part₂.right 0) = 0
  rw [aux_notTighter_mergedG, smul_zero]

/-- Everything the pairwise route encloses is the centre: both its generators
are zero. -/
theorem aux_notTighter_chain_eq_zero {x : ℝ} (hx : x ∈ aux_notTighter_chain.construct) :
    x = 0 := by -- --- PROOF ---
  obtain ⟨a, β, -, -, rfl⟩ := hx
  show (0 : ℝ) + (∑ i : Fin 1, PolyZonotope.monomial aux_notTighter_chain.E a i
      • aux_notTighter_chain.G i) + ∑ j : Fin 2, β j • aux_notTighter_chain.GI j = 0
  rw [Fin.sum_univ_one, Fin.sum_univ_two, aux_notTighter_chainG, aux_notTighter_chainGI0,
    aux_notTighter_chainGI1]
  simp

/-- The group route's independent part is a genuine interval: the two widths
are paid on the two generators separately. -/
theorem aux_notTighter_mem_group {s u : ℝ} (hs : |s| ≤ 1) (hu : |u| ≤ 1) :
    2 * s + -2 * u ∈ aux_notTighter_group.construct := by -- --- PROOF ---
  refine ⟨fun _ => 0, fun j => if (j : ℕ) = 0 then s else u, fun _ => by norm_num, ?_, ?_⟩
  · -- both coefficients are the ones handed in, whichever index asks
    intro j
    by_cases h : (j : ℕ) = 0 <;> simp [h, hs, hu]
  show 2 * s + -2 * u = (0 : ℝ) + (∑ i : Fin 1, PolyZonotope.monomial aux_notTighter_group.E
      (fun _ => (0 : ℝ)) i • aux_notTighter_group.G i) + ∑ j : Fin 2,
        (if (j : ℕ) = 0 then s else u) • aux_notTighter_group.GI j
  rw [Fin.sum_univ_one, Fin.sum_univ_two, aux_notTighter_groupG, aux_notTighter_groupGI0,
    aux_notTighter_groupGI1]
  norm_num
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- A group merge is not always the tighter of the two: here the pairwise
merges reaching the same generator enclose strictly less. -/
theorem PolyZonotope.relaxExpGroup_not_always_tighter :
    ∃ (pZ : PolyZonotope ℝ) (part : Split (Fin pZ.h) into (Fin 1) ⊕ (Fin 2))
      (part₂ : Split (Fin (pZ.relaxExpMulti part).h) into (Fin 0) ⊕ (Fin 2)),
      ((pZ.relaxExpMulti part).relaxExpMulti part₂).construct
        ⊂ (pZ.relaxExpGroup part 0).construct := by -- --- PROOF ---
  refine ⟨aux_notTighter_pZ, aux_notTighter_part, aux_notTighter_part₂, ?_, ?_⟩
  · -- the pairwise route encloses the centre alone, which the group route holds too
    intro x hx
    rw [aux_notTighter_chain_eq_zero hx]
    have h0 := aux_notTighter_mem_group (s := 0) (u := 0) (by norm_num) (by norm_num)
    norm_num at h0
    exact h0
  -- and `4`, which the group route holds, the pairwise route does not
  intro hsub
  have h4 := aux_notTighter_mem_group (s := 1) (u := -1) (by norm_num) (by norm_num)
  norm_num at h4
  have := aux_notTighter_chain_eq_zero (hsub h4)
  norm_num at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
