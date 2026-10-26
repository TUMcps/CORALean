module

public import CORALean.ContSet.Zonotope.Real.Operations.GirardSplit
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Definitions.Coefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# `reduceBox` shrinks as the order rises

`girardSplit`'s ranking permutation does not depend on `o`, only the split point does, so what
`o' ≥ o` drops is a subset of what `o` drops: raising the order only spares generators, never
re-boxes one already kept. A smaller diagonal entry is a smaller box — `[1]` tunes the zonotope
order the same way, against a stated error rather than a guessed one. `aux_girardSplit_right_eq`
reads the same generator off at two orders by matching sorted rank. Below the threshold on both
sides this is the ranking argument; at or past it on either side the box is `ofPoint 0`, a subset
of everything a zonotope's own center already reaches.

## Inputs
* `Z` – zonotope
* `o` – smaller order
* `o'` – larger order

## Hypotheses
* `ho` – orders ordered

## Conclusion
* a higher order gives a smaller box

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The same generator, read off at two orders `o ≤ o'`: shifting the dropped
position by the difference in keep-counts lands on the same sorted rank, the
ranking permutation being the same term at every order. -/
private theorem Zonotope.aux_girardSplit_right_eq (Z : Zonotope (Vec ℝ n)) {o o' : ℕ}
    (hlt : o * n < Z.h) (hlt' : o' * n < Z.h) (ho : o ≤ o')
    (l' : Fin (Z.h - (o' - 1) * n)) : -- --- CONCL ---
    (Z.girardSplit o hlt).right
        ⟨l'.val + ((o' - 1) * n - (o - 1) * n), by
          have hle : (o - 1) * n ≤ Z.h :=
            le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
          have hle' : (o' - 1) * n ≤ Z.h :=
            le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o' 1) (le_refl n)) hlt')
          have hle1 : o - 1 ≤ o' - 1 := by omega
          have hle2 : (o - 1) * n ≤ (o' - 1) * n := Nat.mul_le_mul_right n hle1
          have hl' := l'.isLt
          omega⟩ =
      (Z.girardSplit o' hlt').right l' := by -- --- PROOF ---
  have hle : (o - 1) * n ≤ Z.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
  have hle' : (o' - 1) * n ≤ Z.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o' 1) (le_refl n)) hlt')
  have hle1 : o - 1 ≤ o' - 1 := by omega
  have hle2 : (o - 1) * n ≤ (o' - 1) * n := Nat.mul_le_mul_right n hle1
  unfold Zonotope.girardSplit
  simp only [Partition.right, Partition.on, Partition.reindex, Equiv.trans_apply,
    Equiv.symm_trans_apply, Equiv.apply_eq_iff_eq]
  apply Fin.ext
  simp [Partition.split, Pair.equivSum, finSumFinEquiv_apply_right, Fin.natAdd]
  omega

/-- What the dropped-index nesting buys, per coordinate: boxing fewer
generators at the smaller order `o` can only make the diagonal entry bigger. -/
private theorem Zonotope.aux_reduceByBox_diag_sum_le (Z : Zonotope (Vec ℝ n)) {o o' : ℕ}
    (hlt : o * n < Z.h) (hlt' : o' * n < Z.h) (ho : o ≤ o') (i : Fin n) : -- --- CONCL ---
    (∑ l', |Z.G ((Z.girardSplit o' hlt').right l') i|) ≤
      ∑ l, |Z.G ((Z.girardSplit o hlt).right l) i| := by -- --- PROOF ---
  have hle : (o - 1) * n ≤ Z.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
  have hle' : (o' - 1) * n ≤ Z.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o' 1) (le_refl n)) hlt')
  have hle1 : o - 1 ≤ o' - 1 := by omega
  have hle2 : (o - 1) * n ≤ (o' - 1) * n := Nat.mul_le_mul_right n hle1
  -- shifts a dropped-at-`o'` position up to its dropped-at-`o` counterpart
  let e : Fin (Z.h - (o' - 1) * n) → Fin (Z.h - (o - 1) * n) := fun l' =>
    ⟨l'.val + ((o' - 1) * n - (o - 1) * n), by have := l'.isLt; omega⟩
  have hinj : Function.Injective e := by
    intro a b hab
    apply Fin.ext
    have hab' := congrArg Fin.val hab
    simp only [e] at hab'
    omega
  have heq : ∀ l', Z.G ((Z.girardSplit o hlt).right (e l')) i
      = Z.G ((Z.girardSplit o' hlt').right l') i := by
    intro l'
    rw [Zonotope.aux_girardSplit_right_eq Z hlt hlt' ho l']
  calc (∑ l', |Z.G ((Z.girardSplit o' hlt').right l') i|)
      = ∑ l', |Z.G ((Z.girardSplit o hlt).right (e l')) i| := by simp_rw [heq]
    _ = ∑ j ∈ Finset.image e Finset.univ, |Z.G ((Z.girardSplit o hlt).right j) i| :=
        (Finset.sum_image (f := fun j => |Z.G ((Z.girardSplit o hlt).right j) i|) (g := e)
          (s := Finset.univ) (fun a _ b _ hab => hinj hab)).symm
    _ ≤ ∑ j, |Z.G ((Z.girardSplit o hlt).right j) i| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => abs_nonneg _)

/-- `reduceByBox`'s membership, read off coordinatewise with `.h` already
reduced to `n`, which every diagonal-block proof above would otherwise have to
fight: at coordinate `i` its one active generator carries `β i`. -/
private theorem Zonotope.aux_mem_reduceByBox_iff (Z : Zonotope (Vec ℝ n)) {q r : ℕ}
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (x : Vec ℝ n) : -- --- CONCL ---
    x ∈ (Z.reduceByBox part).construct ↔
      ∃ β : Fin n → ℝ, (∀ j, |β j| ≤ 1) ∧
        ∀ i, x i = (∑ l, |Z.G (part.right l) i|) * β i := by -- --- PROOF ---
  unfold Zonotope.reduceByBox Zonotope.construct
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨β, hβ, hx⟩
    exact ⟨β, hβ, fun i => by
      have h := congrFun hx i
      rwa [Entrywise.add_sum_smul_apply, Pi.zero_apply, zero_add,
        Zonotope.sum_diagonal_mul'] at h⟩
  · rintro ⟨β, hβ, hx⟩
    refine ⟨β, hβ, funext fun i => ?_⟩
    rw [Entrywise.add_sum_smul_apply, Pi.zero_apply, zero_add, Zonotope.sum_diagonal_mul']
    exact hx i


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reduceBox` shrinks as the order rises: raising `o` to `o'` gives a box
contained in the smaller order's. -/
theorem Zonotope.reduceBox_antitone (Z : Zonotope (Vec ℝ n)) {o o' : ℕ}
    (ho : o ≤ o') : -- --- CONCL ---
    (Z.reduceBox o').construct ⊆ (Z.reduceBox o).construct := by -- --- PROOF ---
  unfold Zonotope.reduceBox
  split_ifs with hlt' hlt hlt
  · -- both below the threshold: the dropped generators nest, so does the box
    intro x hx
    obtain ⟨β, hβ, hx⟩ := (Z.aux_mem_reduceByBox_iff (Z.girardSplit o' hlt') x).mp hx
    -- the two box radii, along coordinate `i`: the larger order's, and the smaller order's
    set big : Fin n → ℝ := fun i => ∑ l', |Z.G ((Z.girardSplit o' hlt').right l') i|
    set small : Fin n → ℝ := fun i => ∑ l, |Z.G ((Z.girardSplit o hlt).right l) i|
    have hdrop : ∀ i, |big i * β i| ≤ small i := by
      intro i
      calc |big i * β i|
          ≤ big i := by
            rw [abs_mul, abs_of_nonneg (Finset.sum_nonneg fun l' _ => abs_nonneg _)]
            calc big i * |β i| ≤ big i * 1 :=
                  mul_le_mul_of_nonneg_left (hβ i) (Finset.sum_nonneg fun l' _ => abs_nonneg _)
              _ = big i := mul_one _
        _ ≤ small i := Zonotope.aux_reduceByBox_diag_sum_le Z hlt hlt' ho i
    -- the witness: the same point, scaled back onto the smaller order's box
    refine (Z.aux_mem_reduceByBox_iff (Z.girardSplit o hlt) x).mpr
      ⟨fun i => Zonotope.coefficient (small i) (big i * β i),
        fun i => Zonotope.abs_coefficient_le_one
          (Finset.sum_nonneg fun l _ => abs_nonneg _) (hdrop i), fun i => ?_⟩
    rw [hx i, Zonotope.mul_coefficient (hdrop i)]
  · -- impossible: `o` at or past the threshold forces `o' ≥ o` past it too
    exact absurd (lt_of_le_of_lt (Nat.mul_le_mul_right n ho) hlt') hlt
  · -- `o'` at or past the threshold: the source is already the origin
    intro x hx
    rw [Zonotope.mem_ofPoint_iff] at hx
    subst hx
    exact (Z.aux_mem_reduceByBox_iff (Z.girardSplit o hlt) 0).mpr
      ⟨fun _ => 0, fun _ => by norm_num, fun i => by simp⟩
  · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
