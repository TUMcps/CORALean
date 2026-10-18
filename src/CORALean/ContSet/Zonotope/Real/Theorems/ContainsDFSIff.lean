module

public import CORALean.ContSet.Zonotope.Real.Operations.ContainsDFS
public import CORALean.ContSet.Zonotope.Real.Theorems.ConstructEqConvexHullCorner
public import CORALean.Global.CoeffNormBallEq
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# `containsDFS` decides containment

`[1, Alg. 1]` is exact: `true` iff the zonotope lies in the ellipsotope. A node `σ` is
*good* when every sign vector of full length extending it has value at most `1`. The prune
is sound, `er_{k'}(σ') ≤ h_k(σ)` for every extension (`[1, Eq. 9]`, the triangle
inequality); a node's value is at most the value of some leaf below it (the norm is convex
and a node's point is the midpoint of its children's); and a node is good iff both children
are. So the loop, run on a stack of nodes with values at most `1`, answers whether all of
them are good, with fuel to spare: each step lowers `∑ (2^{m+1-|σ|} - 1)` by one. The
leaves are the corners of the zonotope, the sort a permutation of the generators.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section Search

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- The partial sum a node `σ` stands for, `∑_{i < |σ|} σᵢ gᵢ`. -/
noncomputable def aux_S (g : ℕ → V) (σ : List Bool) : V :=
  ∑ i ∈ Finset.range σ.length, (if σ.getD i false then (1 : ℝ) else -1) • g i

theorem aux_S_append (g : ℕ → V) (σ ρ : List Bool) :
    aux_S g (σ ++ ρ) = aux_S g σ + ∑ i ∈ Finset.Ico σ.length (σ.length + ρ.length),
      (if (σ ++ ρ).getD i false then (1 : ℝ) else -1) • g i := by -- --- PROOF ---
  unfold aux_S
  rw [List.length_append, Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le _)
    (Nat.le_add_right σ.length ρ.length), Finset.range_eq_Ico]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  rw [List.getD_append _ _ _ _ hi.2]

theorem aux_S_snoc (g : ℕ → V) (σ : List Bool) (b : Bool) :
    aux_S g (σ ++ [b]) = aux_S g σ + (if b then (1 : ℝ) else -1) • g σ.length := by
  rw [aux_S_append]
  simp

variable (nrm : V → ℝ) (hadd : ∀ x y, nrm (x + y) ≤ nrm x + nrm y)
  (hsmul : ∀ (a : ℝ) x, nrm (a • x) = |a| * nrm x) (b : V) (g : ℕ → V) (m : ℕ)

/-- Every full-length extension of `σ` has value at most `1`. -/
def aux_Good (σ : List Bool) : Prop :=
  ∀ τ : List Bool, σ <+: τ → τ.length = m → nrm (b + aux_S g τ) ≤ 1

include hadd hsmul in
/-- `[1, Eq. 9]`: an extension's value is below the prune bound. -/
theorem aux_prune {σ τ : List Bool} (hpre : σ <+: τ) (hτ : τ.length ≤ m) :
    nrm (b + aux_S g τ) ≤
      nrm (b + aux_S g σ) + ∑ i ∈ Finset.Ico σ.length m, nrm (g i) := by -- --- PROOF ---
  obtain ⟨ρ, rfl⟩ := hpre
  have h0 : nrm 0 = 0 := by simpa using hsmul 0 0
  rw [aux_S_append, ← add_assoc]
  refine (hadd _ _).trans (add_le_add le_rfl ?_)
  -- the tail's norm is at most the sum of its generators' norms
  refine (Finset.le_sum_of_subadditive nrm h0.le hadd _ _).trans ?_
  have hterm : ∀ i, nrm ((if (σ ++ ρ).getD i false then (1 : ℝ) else -1) • g i) = nrm (g i) :=
    fun i => by rw [hsmul]; split_ifs <;> simp
  simp only [hterm]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl ?_) fun i _ _ => ?_
  · simpa using hτ
  · have := hsmul 0 (g i)
    have h2 := hadd (g i) (-g i)
    have h3 := hsmul (-1) (g i)
    simp only [add_neg_cancel, h0, neg_smul, one_smul, abs_neg, abs_one, one_mul] at h2 h3
    linarith

include hadd hsmul in
/-- A node's value is at most the value of some full-length extension. -/
theorem aux_exists_leaf (k : ℕ) : ∀ σ : List Bool, σ.length + k = m →
    ∃ τ, σ <+: τ ∧ τ.length = m ∧
      nrm (b + aux_S g σ) ≤ nrm (b + aux_S g τ) := by -- --- PROOF ---
  induction k with
  | zero => exact fun σ hσ => ⟨σ, List.prefix_refl σ, by simpa using hσ, le_rfl⟩
  | succ k ih =>
    intro σ hσ
    -- `b + S σ` is the midpoint of the two children's points
    have hmid : b + aux_S g σ = (1 / 2 : ℝ) • (b + aux_S g (σ ++ [true]))
        + (1 / 2 : ℝ) • (b + aux_S g (σ ++ [false])) := by
      rw [aux_S_snoc, aux_S_snoc]; simp only [if_true, if_false, Bool.false_eq_true]; module
    have hle : nrm (b + aux_S g σ) ≤ max (nrm (b + aux_S g (σ ++ [true])))
        (nrm (b + aux_S g (σ ++ [false]))) := by
      rw [hmid]
      refine (hadd _ _).trans ?_
      rw [hsmul, hsmul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have := le_max_left (nrm (b + aux_S g (σ ++ [true]))) (nrm (b + aux_S g (σ ++ [false])))
      have := le_max_right (nrm (b + aux_S g (σ ++ [true]))) (nrm (b + aux_S g (σ ++ [false])))
      linarith
    have hlen : ∀ c : Bool, (σ ++ [c]).length + k = m := fun c => by simp; omega
    rcases le_total (nrm (b + aux_S g (σ ++ [false]))) (nrm (b + aux_S g (σ ++ [true])))
      with hc | hc
    · obtain ⟨τ, hτ, hτl, hτv⟩ := ih (σ ++ [true]) (hlen true)
      exact ⟨τ, (List.prefix_append σ [true]).trans hτ, hτl, (hle.trans (max_le le_rfl hc)).trans
        hτv⟩
    · obtain ⟨τ, hτ, hτl, hτv⟩ := ih (σ ++ [false]) (hlen false)
      exact ⟨τ, (List.prefix_append σ [false]).trans hτ, hτl,
        (hle.trans (max_le hc le_rfl)).trans hτv⟩

/-- A node is good iff both its children are. -/
theorem aux_good_iff {σ : List Bool} (hσ : σ.length < m) :
    aux_Good nrm b g m σ ↔
      aux_Good nrm b g m (σ ++ [true]) ∧ aux_Good nrm b g m (σ ++ [false]) := by -- --- PROOF ---
  constructor
  · exact fun h => ⟨fun τ hτ => h τ ((List.prefix_append _ _).trans hτ),
      fun τ hτ => h τ ((List.prefix_append _ _).trans hτ)⟩
  -- a longer extension continues with one sign or the other
  · rintro ⟨hp, hm⟩ τ ⟨ρ, rfl⟩ hτ
    cases ρ with
    | nil => simp at hτ; omega
    | cons c ρ =>
      have : σ ++ c :: ρ = (σ ++ [c]) ++ ρ := by simp
      rw [this] at hτ ⊢
      cases c
      · exact hm _ (List.prefix_append _ _) hτ
      · exact hp _ (List.prefix_append _ _) hτ

/-- The fuel a stack still needs: each node weighs the size of its subtree. -/
def aux_w (σ : List Bool) : ℕ := 2 ^ (m + 1 - σ.length) - 1

include hadd hsmul in
theorem aux_loop (f : ℕ) : -- --- STMT ---
    ∀ stack : List (List Bool),
    (∀ σ ∈ stack, σ.length ≤ m ∧ nrm (b + aux_S g σ) ≤ 1) →
    (stack.map (aux_w m)).sum < f →
    (Zonotope.containsDFS.loop (fun σ => nrm (b + aux_S g σ))
        (fun σ => nrm (b + aux_S g σ) + ∑ i ∈ Finset.Ico σ.length m, nrm (g i)) f stack = true ↔
      ∀ σ ∈ stack, aux_Good nrm b g m σ) := by -- --- PROOF ---
  induction f with
  | zero => intro _ _ h; simp at h
  | succ f ih =>
    rintro (_ | ⟨σ, rest⟩) hinv hμ
    · simp [Zonotope.containsDFS.loop]
    obtain ⟨hσm, hσv⟩ := hinv σ (List.mem_cons_self ..)
    have hrest : ∀ τ ∈ rest, τ.length ≤ m ∧ nrm (b + aux_S g τ) ≤ 1 :=
      fun τ hτ => hinv τ (List.mem_cons_of_mem _ hτ)
    have hwσ : 1 ≤ aux_w m σ := by
      unfold aux_w
      have : 2 ≤ 2 ^ (m + 1 - σ.length) :=
        Nat.le_self_pow (by omega) 2
      omega
    simp only [List.map_cons, List.sum_cons] at hμ
    simp only [Zonotope.containsDFS.loop, List.forall_mem_cons]
    split_ifs with hh hmax hge
    -- pruned: `σ` is good, and the rest is the recursion
    · rw [ih rest hrest (by omega)]
      exact ⟨fun h => ⟨fun τ hτ hτl => (aux_prune nrm hadd hsmul b g m hτ (by omega)).trans hh,
        h⟩, fun h => h.2⟩
    -- a child above `1`: some leaf below `σ` is above `1`
    · have hlt : σ.length < m := by
        by_contra hlt
        have : σ.length = m := by omega
        simp [this] at hh
        linarith
      simp only [false_iff, not_and]
      intro hg _
      obtain ⟨hgp, hgm⟩ := (aux_good_iff nrm b g m hlt).mp hg
      have hlen : ∀ c : Bool, (σ ++ [c]).length + (m - (σ.length + 1)) = m := fun c => by
        simp; omega
      rcases lt_max_iff.mp hmax with hc | hc
      · obtain ⟨τ, hτ, hτl, hτv⟩ := aux_exists_leaf nrm hadd hsmul b g m _ (σ ++ [false])
          (hlen false)
        linarith [hgm τ hτ hτl]
      · obtain ⟨τ, hτ, hτl, hτv⟩ := aux_exists_leaf nrm hadd hsmul b g m _ (σ ++ [true])
          (hlen true)
        linarith [hgp τ hτ hτl]
    -- both children fit: recurse on them
    all_goals
      have hlt : σ.length < m := by
        by_contra hlt
        have : σ.length = m := by omega
        simp [this] at hh
        linarith
      push Not at hmax
      -- a child weighs half its parent, less one
      have hwc : ∀ c : Bool, 2 * aux_w m (σ ++ [c]) + 1 = aux_w m σ := fun c => by
        unfold aux_w
        simp only [List.length_append, List.length_singleton]
        have : m + 1 - σ.length = (m + 1 - (σ.length + 1)) + 1 := by omega
        rw [this, pow_succ]
        have : 1 ≤ 2 ^ (m + 1 - (σ.length + 1)) := Nat.one_le_two_pow
        omega
      have hinv' : ∀ c : Bool, (σ ++ [c]).length ≤ m ∧ nrm (b + aux_S g (σ ++ [c])) ≤ 1 := by
        intro c
        refine ⟨by simp; omega, ?_⟩
        cases c
        · exact (le_max_left _ _).trans hmax
        · exact (le_max_right _ _).trans hmax
      -- the recursion's answer is the children's goodness, so `σ`'s
      rw [ih _ ?_ ?_, (aux_good_iff nrm b g m hlt)]
      · simp only [List.forall_mem_cons]
        tauto
      · simp only [List.forall_mem_cons]
        exact ⟨hinv' _, hinv' _, hrest⟩
      · simp only [List.map_cons, List.sum_cons]
        have h1 := hwc true
        have h2 := hwc false
        omega

end Search


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.containsDFS_iff [FiniteDimensional ℝ E] (Z : Zonotope (Vec ℝ n))
    (H : E →ₗ[ℝ] Vec ℝ n) (hH : Function.Surjective H) (d : Vec ℝ n) :
    Z.containsDFS H d = true ↔
      Z.construct ⊆ {x | ∃ β : E, ‖β‖ ≤ 1 ∧ x = d + H β} := by -- --- PROOF ---
  classical
  set nrm := coeffNorm H with hnrm
  have hadd : ∀ x y, nrm (x + y) ≤ nrm x + nrm y := fun x y => coeffNorm_add_le H (hH x) (hH y)
  have hsmul : ∀ (a : ℝ) x, nrm (a • x) = |a| * nrm x := fun a x => coeffNorm_smul H (hH x) a
  set ord := (List.finRange Z.h).mergeSort fun i j =>
    if nrm (Z.G j) ≤ nrm (Z.G i) then true else false with hord
  set g : ℕ → Vec ℝ n := fun i => (ord.map Z.G).getD i 0 with hg
  -- the sort is a permutation of the generators, read as an equivalence of indices
  have hperm : ord.Perm (List.finRange Z.h) := List.mergeSort_perm _ _
  have hlen : ord.length = Z.h := by rw [hperm.length_eq, List.length_finRange]
  have hnd : ord.Nodup := hperm.nodup_iff.mpr (List.nodup_finRange _)
  have hall : ∀ j, j ∈ ord := fun j => hperm.mem_iff.mpr (List.mem_finRange j)
  let e : Fin ord.length ≃ Fin Z.h := List.Nodup.getEquivOfForallMemList ord hnd hall
  -- a leaf's point is a corner
  have hleaf : ∀ τ : List Bool, τ.length = Z.h →
      Z.c - d + aux_S g τ = Z.corner (fun j => τ.getD (e.symm j) false) - d := by
    intro τ hτ
    unfold aux_S Zonotope.corner
    have hrange : Finset.range τ.length = Finset.range ord.length := by rw [hτ, hlen]
    rw [hrange, ← Fin.sum_univ_eq_sum_range
      (fun i => (if τ.getD i false then (1 : ℝ) else -1) • g i)]
    rw [← Fintype.sum_equiv e.symm
      (fun j => (if τ.getD (e.symm j) false then (1 : ℝ) else -1) • g (e.symm j))
      (fun k : Fin ord.length => (if τ.getD k false then (1 : ℝ) else -1) • g k) fun _ => rfl]
    -- the `k`-th sorted generator is generator `e k`
    have hgk : ∀ k : Fin ord.length, g k = Z.G (e k) := fun k => by
      simp only [hg, e, List.Nodup.getEquivOfForallMemList_apply]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map]
      rfl
    simp only [hgk, Equiv.apply_symm_apply]
    abel
  have hcorner : ∀ s : Fin Z.h → Bool, ∃ τ : List Bool, τ.length = Z.h ∧
      (fun j => τ.getD (e.symm j) false) = s := by
    intro s
    refine ⟨List.ofFn fun k : Fin ord.length => s (e k), by simp [hlen], funext fun j => ?_⟩
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    simp
  -- the circumbody is `{ν(· - d) ≤ 1}`, which is convex
  obtain ⟨-, hball, -⟩ := coeffNorm_ball_eq H hH
  have hcirc : {x | ∃ β : E, ‖β‖ ≤ 1 ∧ x = d + H β} = {x | nrm (x - d) ≤ 1} := by
    ext x
    have := congrArg (fun S => x - d ∈ S) hball
    simp only [Set.mem_setOf_eq, Set.mem_image, Metric.mem_closedBall, dist_zero_right,
      eq_iff_iff] at this
    simp only [Set.mem_setOf_eq, hnrm, this]
    exact ⟨fun ⟨β, hβ, he⟩ => ⟨β, hβ, by rw [he]; abel⟩,
      fun ⟨β, hβ, he⟩ => ⟨β, hβ, by rw [he]; abel⟩⟩
  -- convex: the triangle inequality with homogeneity
  have hconv : Convex ℝ {x | nrm (x - d) ≤ 1} := by
    intro x hx y hy a c ha hc hac
    have e' : a • x + c • y - d = a • (x - d) + c • (y - d) :=
      calc a • x + c • y - d = a • x + c • y - (a + c) • d := by rw [hac, one_smul]
        _ = a • (x - d) + c • (y - d) := by module
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [e']
    refine (hadd _ _).trans ?_
    rw [hsmul, hsmul, abs_of_nonneg ha, abs_of_nonneg hc]
    nlinarith
  have hsub : Z.construct ⊆ {x | ∃ β : E, ‖β‖ ≤ 1 ∧ x = d + H β} ↔
      ∀ s, nrm (Z.corner s - d) ≤ 1 := by
    rw [hcirc, Z.construct_eq_convexHull_corner]
    constructor
    · exact fun h s => h (subset_convexHull ℝ _ ⟨s, rfl⟩)
    · exact fun h => convexHull_min (by rintro _ ⟨s, rfl⟩; exact h s) hconv
  -- the root is good iff every corner is in the circumbody
  have hgood : aux_Good nrm (Z.c - d) g Z.h [] ↔ ∀ s, nrm (Z.corner s - d) ≤ 1 := by
    constructor
    · intro h s
      obtain ⟨τ, hτ, rfl⟩ := hcorner s
      rw [← hleaf τ hτ]
      exact h τ (List.nil_prefix) hτ
    · intro h τ _ hτ
      rw [hleaf τ hτ]
      exact h _
  rw [hsub, ← hgood]
  -- the algorithm: the root's check, then the loop on `[[]]`
  have hroot : nrm (Z.c - d + aux_S g []) = nrm (Z.c - d) := by simp [aux_S]
  show (if nrm (Z.c - d) > 1 then false else Zonotope.containsDFS.loop
    (fun σ => nrm (Z.c - d + aux_S g σ))
    (fun σ => nrm (Z.c - d + aux_S g σ) + ∑ i ∈ Finset.Ico σ.length Z.h, nrm (g i))
    (2 ^ (Z.h + 1)) [[]]) = true ↔ _
  split_ifs with hM
  · simp only [false_iff]
    intro hg0
    obtain ⟨τ, -, hτl, hτv⟩ := aux_exists_leaf nrm hadd hsmul (Z.c - d) g Z.h Z.h [] (by simp)
    linarith [hg0 τ (List.nil_prefix) hτl]
  · rw [aux_loop nrm hadd hsmul (Z.c - d) g Z.h _ [[]] (by simp [hroot]; linarith)
      (by simp [aux_w])]
    simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
