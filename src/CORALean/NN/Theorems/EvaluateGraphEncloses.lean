module

public import CORALean.NN.Operations.EvaluateGraph
public import CORALean.NN.Layers.Theorems.ProductLineEncloses
public import CORALean.ContSet.Zonotope.Float.Theorems.ContainsAtMtimes
public import CORALean.ContSet.Zonotope.Float.Theorems.ContainsAtPlus
public import CORALean.ContSet.Zonotope.Float.Theorems.MemToSetIffContainsAt
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Zonotope.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `GraphNet.evaluateGraph` encloses the graph network

The exact network's last output lies in the zonotope `evaluateGraph` computes. The invariant is
the one CORA.cpp's shared factor list rests on: one vector of weights `β ∈ [-1, 1]^ℕ` such that
every output so far is in its zonotope at `β` (`Zonotope.ContainsAt` at `β`'s first entries), and
no output has more generators than the latest. A linear part keeps `β`: `Zonotope.mtimes` keeps
the weights, padding adds zero generators, and a residual's generators are added to the first ones,
which are its own. An activation extends `β` past the generators so far by the weights of its
errors (`Zonotope.plus`), so the earlier outputs keep theirs. Each error is in its box by the
layer's relaxation (`Relaxation.Encloses`) or by `productLine_encloses` at `β`.

## Inputs
* `k` – the output dimension
* `F` – the float network
* `R` – the exact network
* `X` – the input set
* `x` – a point of it

## Hypotheses
* `h` – `R` has `F`'s weights, and activations that `F`'s enclose
* `hx` – `x` is in `X`

## Conclusion
* the exact network's output at `x` is in `F.evaluateGraph X`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum over the first `h₁` indices of a function zero from `h₂ ≤ h₁` on is the sum over `h₂`. -/
private theorem GraphNet.aux_sum_prefix {h₁ h₂ : ℕ} (hle : h₂ ≤ h₁) (f : ℕ → ℝ)
    (hf : ∀ k, h₂ ≤ k → f k = 0) :
    ∑ j : Fin h₁, f j = ∑ j : Fin h₂, f j := by
  rw [Fin.sum_univ_eq_sum_range f h₁, Fin.sum_univ_eq_sum_range f h₂]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Finset.sum_range_add, Finset.sum_eq_zero fun k _ => hf _ (Nat.le_add_right _ _), add_zero]

/-- At `β` the weights of `Z` are `β`'s first entries. -/
private theorem GraphNet.aux_containsAt_congr {Z : Zonotope (Vec 𝕋 n)} {β β' : ℕ → ℝ}
    {x : Vec ℝ n} (hβ : ∀ j < Z.h, β' j = β j) (h : Z.ContainsAt (fun j => β j.1) x) :
    Z.ContainsAt (fun j => β' j.1) x := by
  have e : (fun j : Fin Z.h => β' j.1) = fun j => β j.1 := funext fun j => hβ j.1 j.2
  rw [e]
  exact h

/-- Zero generators up to `rows` keep the weights. -/
private theorem GraphNet.aux_padRows {Z : Zonotope (Vec 𝕋 n)} {β : ℕ → ℝ} {x : Vec ℝ n}
    (hβ : ∀ j, |β j| ≤ 1) (h : Z.ContainsAt (fun j => β j.1) x) (rows : ℕ) : -- --- CONCL ---
    (GraphNet.step_padRows Z rows).ContainsAt (fun j => β j.1) x := by -- --- PROOF ---
  obtain ⟨-, e, he, hx⟩ := h
  refine ⟨fun j => hβ _, e, he, fun i => ?_⟩
  rw [hx i]
  -- the padded sum is the sum over the first `Z.h` weights
  let f : ℕ → ℝ := fun k => if hk : k < Z.h then toReal (Z.G ⟨k, hk⟩ i) * β k else 0
  have h₁ : ∑ j : Fin (GraphNet.step_padRows Z rows).h,
      toReal ((GraphNet.step_padRows Z rows).G j i) * β j = ∑ j : Fin (Z.h + (rows - Z.h)), f j :=
    Finset.sum_congr rfl fun j _ => by
      simp only [GraphNet.step_padRows, f]
      split_ifs <;> simp [toReal_zero]
  have h₂ : ∑ j : Fin Z.h, toReal (Z.G j i) * β j = ∑ j : Fin Z.h, f j :=
    Finset.sum_congr rfl fun j _ => by simp [f, j.2]
  rw [h₁, h₂, GraphNet.aux_sum_prefix (Nat.le_add_right _ _) f fun k hk => by
    simp [f, not_lt.mpr hk]]
  rfl

/-- `Z₂`'s generators on the first ones of `Z₁` keep the weights, with `Z₂.h ≤ Z₁.h`. -/
private theorem GraphNet.aux_addRows {Z₁ Z₂ : Zonotope (Vec 𝕋 n)} {β : ℕ → ℝ} {x₁ x₂ : Vec ℝ n}
    (hle : Z₂.h ≤ Z₁.h) (hβ : ∀ j, |β j| ≤ 1) (h₁ : Z₁.ContainsAt (fun j => β j.1) x₁)
    (h₂ : Z₂.ContainsAt (fun j => β j.1) x₂) : -- --- CONCL ---
    (GraphNet.step_addRows Z₁ Z₂).ContainsAt (fun j => β j.1) (x₁ + x₂) := by -- --- PROOF ---
  obtain ⟨-, e₁, he₁, hx₁⟩ := h₁
  obtain ⟨-, e₂, he₂, hx₂⟩ := h₂
  -- the stored generators and their gaps
  have hG : ∀ (j : Fin Z₁.h) i, (GraphNet.step_addRows Z₁ Z₂).G j i =
      if hj : j.1 < Z₂.h then addDown (Z₁.G j i) (Z₂.G ⟨j.1, hj⟩ i) else Z₁.G j i :=
    fun _ _ => rfl
  let gap : Mat 𝕋 n Z₁.h := fun i j =>
    if hj : j.1 < Z₂.h then subUp (addUp (Z₁.G j i) (Z₂.G ⟨j.1, hj⟩ i))
      (addDown (Z₁.G j i) (Z₂.G ⟨j.1, hj⟩ i)) else zero
  -- the exact column, and its distance from the stored one
  let ex : Fin n → Fin Z₁.h → ℝ := fun i j =>
    if hj : j.1 < Z₂.h then toReal (Z₁.G j i) + toReal (Z₂.G ⟨j.1, hj⟩ i) else toReal (Z₁.G j i)
  let Δ : Mat ℝ n Z₁.h := fun i j => ex i j - toReal ((GraphNet.step_addRows Z₁ Z₂).G j i)
  have hΔ : ∀ i j, |Δ i j| ≤ toReal (gap i j) := by
    -- a shared column is rounded down, within its gap; a copied one is exact
    intro i j
    simp only [Δ, ex, gap, hG]
    split_ifs with hj
    · have := addDown_le_add (Z₁.G j i) (Z₂.G ⟨j.1, hj⟩ i)
      have := add_le_addUp (Z₁.G j i) (Z₂.G ⟨j.1, hj⟩ i)
      have := sub_le_subUp (addUp (Z₁.G j i) (Z₂.G ⟨j.1, hj⟩ i))
        (addDown (Z₁.G j i) (Z₂.G ⟨j.1, hj⟩ i))
      rw [abs_le]
      constructor <;> linarith
    · simp [toReal_zero]
  -- the boxes: the operands', the center's rounding, the generators' rounding
  have hg := Zonotope.mem_generatorError (β := fun j : Fin Z₁.h => β j.1) hΔ fun j => hβ _
  have hr := Interval.sub_mem_residual (stored := fun i => addDown (Z₁.c i) (Z₂.c i))
    (x := fun i => toReal (Z₁.c i) + toReal (Z₂.c i))
    (lo := fun i => addDown (Z₁.c i) (Z₂.c i)) (hi := fun i => addUp (Z₁.c i) (Z₂.c i))
    (fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩)
  refine ⟨fun j => hβ _, _, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _
    ⟨_, Interval.plus_outer _ _ ⟨e₁, he₁, e₂, he₂, rfl⟩, _, hr, rfl⟩, _, hg, rfl⟩, fun i => ?_⟩
  -- the second operand's sum over the first `Z₁.h` weights
  have hs₂ : ∑ j : Fin Z₂.h, toReal (Z₂.G j i) * β j =
      ∑ j : Fin Z₁.h, (ex i j - toReal (Z₁.G j i)) * β j := by
    let f : ℕ → ℝ := fun k => if hk : k < Z₂.h then toReal (Z₂.G ⟨k, hk⟩ i) * β k else 0
    have ha : ∑ j : Fin Z₁.h, (ex i j - toReal (Z₁.G j i)) * β j = ∑ j : Fin Z₁.h, f j :=
      Finset.sum_congr rfl fun j _ => by
        simp only [ex, f]
        split_ifs <;> ring
    have hb : ∑ j : Fin Z₂.h, toReal (Z₂.G j i) * β j = ∑ j : Fin Z₂.h, f j :=
      Finset.sum_congr rfl fun j _ => by simp [f, j.2]
    rw [ha, hb, GraphNet.aux_sum_prefix hle f fun k hk => by simp [f, not_lt.mpr hk]]
  -- the stored generators plus their errors are both operands' generators
  have hsum : ∑ j : Fin Z₁.h, toReal ((GraphNet.step_addRows Z₁ Z₂).G j i) * β j
      + ∑ j, Δ i j * β j =
      ∑ j : Fin Z₁.h, toReal (Z₁.G j i) * β j + ∑ j : Fin Z₂.h, toReal (Z₂.G j i) * β j := by
    rw [hs₂, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [Δ]; ring
  show x₁ i + x₂ i = toReal (addDown (Z₁.c i) (Z₂.c i))
    + ∑ j : Fin Z₁.h, toReal ((GraphNet.step_addRows Z₁ Z₂).G j i) * β j
    + (e₁ i + e₂ i + (toReal (Z₁.c i) + toReal (Z₂.c i) - toReal (addDown (Z₁.c i) (Z₂.c i)))
      + ∑ j, Δ i j * β j)
  rw [hx₁ i, hx₂ i]
  linarith [hsum]

/-- The plus of the bias, a zonotope without generators, keeps the weights. -/
private theorem GraphNet.aux_plusPoint {Z : Zonotope (Vec 𝕋 n)} {β : ℕ → ℝ} {x : Vec ℝ n}
    (h : Z.ContainsAt (fun j => β j.1) x) (b : Vec 𝕋 n) : -- --- CONCL ---
    (Z.plus (Zonotope.point b)).ContainsAt (fun j => β j.1) (x + toRealVec b) := by -- --- PROOF ---
  have hb : (Zonotope.point b).ContainsAt (fun j => j.elim0) (toRealVec b) := by
    refine ⟨fun j => j.elim0, 0, fun i => ?_, fun i => ?_⟩
    · show toReal (zero : 𝕋) ≤ 0 ∧ (0 : ℝ) ≤ toReal (zero : 𝕋)
      rw [toReal_zero]
      exact ⟨le_rfl, le_rfl⟩
    · simp [Zonotope.point, toRealVec]
  have key := Zonotope.containsAt_plus h hb
  have e : (Fin.append (fun j : Fin Z.h => β j.1) fun j : Fin 0 => j.elim0) =
      fun j : Fin (Z.h + 0) => β j.1 :=
    funext fun j => Fin.addCases (fun j' => by simp) (fun j' => j'.elim0) j
  convert key using 2
  exact (congrFun e _).symm

/-- The plus of a layer's errors, at weights `γ`, extends `β` past `Z₁`'s generators by `γ`. -/
private theorem GraphNet.aux_plusExtend {Z₁ Z₂ : Zonotope (Vec 𝕋 n)} {β : ℕ → ℝ} {γ : Vec ℝ Z₂.h}
    {x₁ x₂ : Vec ℝ n} (hβ : ∀ j, |β j| ≤ 1) (h₁ : Z₁.ContainsAt (fun j => β j.1) x₁)
    (h₂ : Z₂.ContainsAt γ x₂) : -- --- CONCL ---
    ∃ β' : ℕ → ℝ, (∀ j, |β' j| ≤ 1) ∧ (∀ j < Z₁.h, β' j = β j) ∧
      (Z₁.plus Z₂).ContainsAt (fun j => β' j.1) (x₁ + x₂) := by -- --- PROOF ---
  let β' : ℕ → ℝ := fun j =>
    if j < Z₁.h then β j else if hj : j - Z₁.h < Z₂.h then γ ⟨j - Z₁.h, hj⟩ else 0
  refine ⟨β', fun j => ?_, fun j hj => if_pos hj, ?_⟩
  · simp only [β']
    split_ifs
    · exact hβ j
    · exact h₂.1 _
    · simp
  · have key := Zonotope.containsAt_plus h₁ h₂
    have e : Fin.append (fun j : Fin Z₁.h => β j.1) γ = fun j : Fin (Z₁.h + Z₂.h) => β' j.1 := by
      funext j
      refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
      · simp [β', j'.2]
      · simp [β']
    convert key using 2
    exact (congrFun e _).symm

/-- The box without generators holds every point of the box, at no weights. -/
private theorem GraphNet.aux_errorBox (I : Interval (Vec 𝕋 n)) {x : Vec ℝ n} (hx : x ∈ I.toSet)
    (γ : Vec ℝ 0) : -- --- CONCL ---
    (GraphNet.step_errorBox I).ContainsAt γ x := by -- --- PROOF ---
  refine ⟨fun j => j.elim0, fun i => x i - toReal (I.center i), fun i => ?_, fun i => ?_⟩
  · have h1 : toReal (I.inf i) ≤ x i := (hx i).1
    have h2 : x i ≤ toReal (I.sup i) := (hx i).2
    have h3 := sub_le_subUp (I.sup i) (I.center i)
    have h4 := sub_le_subUp (I.center i) (I.inf i)
    show toReal (neg (I.radiusFrom i)) ≤ x i - toReal (I.center i)
      ∧ x i - toReal (I.center i) ≤ toReal (I.radiusFrom i)
    simp only [toReal_neg, Interval.radiusFrom, toReal_maximum]
    constructor
    · linarith [le_max_right (toReal (subUp (I.sup i) (I.center i)))
        (toReal (subUp (I.center i) (I.inf i)))]
    · linarith [le_max_left (toReal (subUp (I.sup i) (I.center i)))
        (toReal (subUp (I.center i) (I.inf i)))]
  · simp [GraphNet.step_errorBox]

/-- A layer's errors hold every point of their box, at some weights. -/
private theorem GraphNet.aux_errors (slots : Bool) (I : Interval (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : x ∈ I.toSet) :
    ∃ γ, (GraphNet.step_errors slots I).ContainsAt γ x := by
  cases slots
  · refine ⟨fun j => j.elim0, ?_⟩
    exact GraphNet.aux_errorBox I hx _
  · exact Zonotope.mem_toSet_iff_containsAt.mp (Interval.zonotope_contains I hx)

/-- A point of the box `[subDown o e, addUp o e]` when it is within `e` of `o`. -/
private theorem GraphNet.aux_mem_band {o e : 𝕋} {t : ℝ} (h : |t - toReal o| ≤ toReal e) :
    toReal (subDown o e) ≤ t ∧ t ≤ toReal (addUp o e) := by
  have h1 := subDown_le_sub o e
  have h2 := add_le_addUp o e
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- The product's slope map: `c_b a + c_a b` on the first half, `0` on the second. -/
private theorem GraphNet.aux_productSlope {k : ℕ} (c : Vec 𝕋 (k + k)) (z : Vec ℝ (k + k))
    (i : Fin (k + k)) : -- --- CONCL ---
    (toRealMat (GraphNet.step_productSlope c) *ᵥ z) i = Fin.addCases
      (fun i' => toReal (c (Fin.natAdd k i')) * z (Fin.castAdd k i')
        + toReal (c (Fin.castAdd k i')) * z (Fin.natAdd k i')) (fun _ => 0) i := by -- --- PROOF ---
  refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
  · have hne : Fin.castAdd k i' ≠ Fin.natAdd k i' := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    have hne' : Fin.addNat i' k ≠ Fin.castAdd k i' := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    show ∑ j, toReal (GraphNet.step_productSlope c (Fin.castAdd k i') j) * z j = _
    rw [Fintype.sum_eq_add (Fin.castAdd k i') (Fin.natAdd k i') hne, Fin.addCases_left]
    · simp [GraphNet.step_productSlope, hne']
    · rintro j ⟨h1, h2⟩
      simp only [GraphNet.step_productSlope, Fin.addCases_left]
      rw [if_neg h1, if_neg h2, toReal_zero, zero_mul]
  · show ∑ j, toReal (GraphNet.step_productSlope c (Fin.natAdd k i') j) * z j = _
    simp only [GraphNet.step_productSlope, Fin.addCases_right]
    rw [toReal_zero]
    simp

/-- The activation keeps the earlier weights and extends them by its errors'. -/
private theorem GraphNet.aux_activate {m : ℕ} {a : GraphAct 𝕋 m} {r : Real.GraphAct m}
    (ha : a.Images r) {Z : Zonotope (Vec 𝕋 m)} {β : ℕ → ℝ} {z : Vec ℝ m}
    (hβ : ∀ j, |β j| ≤ 1) (hz : Z.ContainsAt (fun j => β j.1) z) : -- --- CONCL ---
    ∃ β' : ℕ → ℝ, (∀ j, |β' j| ≤ 1) ∧ (∀ j < Z.h, β' j = β j) ∧
      Z.h ≤ (GraphNet.step_activate a Z).h ∧
      (GraphNet.step_activate a Z).ContainsAt (fun j => β' j.1) (r.apply z) := by -- --- PROOF ---
  cases ha with
  | identity => exact ⟨β, hβ, fun _ _ => rfl, le_rfl, hz⟩
  | elementwise slots hR =>
    rename_i R σ
    have hzI : z ∈ Z.interval.toSet :=
      Zonotope.interval_contains Z (Zonotope.mem_toSet_iff_containsAt.mpr ⟨_, hz⟩)
    let I := Z.interval
    let s : Vec 𝕋 m := fun i => R.slope (I.inf i) (I.sup i)
    -- the slope map, entrywise
    have hD : ∀ i, (toRealMat (diagonalBlock s) *ᵥ z) i = toReal (s i) * z i := fun i => by
      have : toRealMat (diagonalBlock s) = Matrix.diagonal (toRealVec s) := by
        funext i l
        exact toReal_diagonalBlock s i l
      rw [this, Matrix.mulVec_diagonal]
      rfl
    -- the errors, in the relaxation's box
    have hw : (fun i => σ (z i) - (toRealMat (diagonalBlock s) *ᵥ z) i) ∈ (R.box I).toSet := by
      intro i
      show toReal ((R.box I).inf i) ≤ σ (z i) - (toRealMat (diagonalBlock s) *ᵥ z) i
        ∧ σ (z i) - (toRealMat (diagonalBlock s) *ᵥ z) i ≤ toReal ((R.box I).sup i)
      rw [hD i]
      refine GraphNet.aux_mem_band ?_
      have := hR.sound (hzI i).1 (hzI i).2
      rw [show σ (z i) - toReal (s i) * z i - toReal (R.offset (I.inf i) (I.sup i)) =
        σ (z i) - (toReal (R.slope (I.inf i) (I.sup i)) * z i
          + toReal (R.offset (I.inf i) (I.sup i))) by simp only [s]; ring]
      exact this
    -- the errors at new weights after the slope map's, which keeps `β`
    obtain ⟨γ, hγ⟩ := GraphNet.aux_errors slots (R.box I) hw
    obtain ⟨β', hβ', hagree, hmem⟩ :=
      GraphNet.aux_plusExtend hβ (Zonotope.containsAt_mtimes (diagonalBlock s) hz) hγ
    have hstep : GraphNet.step_activate (.elementwise R slots) Z =
        (Zonotope.mtimes (diagonalBlock s) Z).plus (GraphNet.step_errors slots (R.box I)) := by
      simp [GraphNet.step_activate, s, I]
    rw [hstep]
    refine ⟨β', hβ', hagree, Nat.le_add_right _ _, ?_⟩
    convert hmem using 1
    funext i
    simp [Real.GraphAct.apply]
  | product slots hτ hw₁ hw₂ =>
    rename_i k p τ w₂ w₁
    obtain ⟨-, e, he, hze⟩ := id hz
    let line := GraphNet.step_productLines p τ w₂ w₁ Z
    let D := GraphNet.step_productSlope Z.c
    -- the error box's radii bound the error
    have hρ : ∀ i, |e i| ≤ toReal (maximum (Z.I_error.sup i) (neg (Z.I_error.inf i))) := by
      intro i
      have h1 : toReal (Z.I_error.inf i) ≤ e i := (he i).1
      have h2 : e i ≤ toReal (Z.I_error.sup i) := (he i).2
      rw [toReal_maximum, toReal_neg, abs_le]
      constructor
      · linarith [le_max_right (toReal (Z.I_error.sup i)) (-toReal (Z.I_error.inf i))]
      · linarith [le_max_left (toReal (Z.I_error.sup i)) (-toReal (Z.I_error.inf i))]
    -- the errors, in the box of the lines
    have hw : (fun i => (Real.GraphAct.product k).apply z i - (toRealMat D *ᵥ z) i) ∈
        (GraphNet.step_productBox line).toSet := by
      intro i
      show toReal ((GraphNet.step_productBox line).inf i)
          ≤ (Real.GraphAct.product k).apply z i - (toRealMat D *ᵥ z) i
        ∧ (Real.GraphAct.product k).apply z i - (toRealMat D *ᵥ z) i
          ≤ toReal ((GraphNet.step_productBox line).sup i)
      rw [GraphNet.aux_productSlope]
      -- the first half by `productLine_encloses` at `β`, the second is `0`
      refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
      · simp only [GraphNet.step_productBox, Real.GraphAct.apply, Fin.addCases_left]
        refine GraphNet.aux_mem_band ?_
        have key := productLine_encloses p hτ (hw₁ Z.h) hw₂ (Z.c (Fin.castAdd k i'))
          (Z.c (Fin.natAdd k i')) (fun j => Z.G j (Fin.castAdd k i'))
          (fun j => Z.G j (Fin.natAdd k i')) _ _ (β := fun j : Fin Z.h => β j.1)
          (fun j => hβ _) (hρ (Fin.castAdd k i')) (hρ (Fin.natAdd k i'))
        simp only [] at key
        -- the two halves of `z` at `β` are the operands of the line
        rw [hze (Fin.castAdd k i'), hze (Fin.natAdd k i')]
        convert key using 2
        all_goals first | rfl | (simp only [line, GraphNet.step_productLines]; ring)
      · simp only [GraphNet.step_productBox, Real.GraphAct.apply, Fin.addCases_right]
        rw [toReal_zero]
        simp
    -- the errors at new weights, as for an element-wise activation
    obtain ⟨γ, hγ⟩ := GraphNet.aux_errors slots (GraphNet.step_productBox line) hw
    obtain ⟨β', hβ', hagree, hmem⟩ :=
      GraphNet.aux_plusExtend hβ (Zonotope.containsAt_mtimes D hz) hγ
    have hstep : GraphNet.step_activate (.product k p τ w₂ w₁ slots) Z =
        (Zonotope.mtimes D Z).plus (GraphNet.step_errors slots (GraphNet.step_productBox line)) :=
      by simp [GraphNet.step_activate, D, line]
    rw [hstep]
    refine ⟨β', hβ', hagree, Nat.le_add_right _ _, ?_⟩
    convert hmem using 1
    funext i
    simp

/-- The linear part keeps the weights, and has at least the generators so far. -/
private theorem GraphNet.aux_linear {Γ : List ℕ} {m : ℕ} (L : GraphLayer 𝕋 Γ m)
    (a : Real.GraphAct m) {E : GraphEnv 𝒵[𝕋] Γ}
    {e : GraphEnv (Vec ℝ) Γ} {β : ℕ → ℝ} {rows : ℕ} (hβ : ∀ j, |β j| ≤ 1)
    (hE : ∀ i, (E i).h ≤ rows ∧ (E i).ContainsAt (fun j => β j.1) (e i)) : -- --- CONCL ---
    rows ≤ (GraphNet.step_linear L E rows).h ∧
      (GraphNet.step_linear L E rows).ContainsAt (fun j => β j.1)
        ((L.toReal a).preact e) := by -- --- PROOF ---
  -- 1. the source through W, plus b, padded
  set Z₀ := GraphNet.step_padRows ((Zonotope.mtimes L.W (E L.src)).plus
    (Zonotope.point L.b)).materialise rows with hZ₀
  have h₀ : Z₀.ContainsAt (fun j => β j.1) (toRealMat L.W *ᵥ e L.src + toRealVec L.b) := by
    refine GraphNet.aux_padRows hβ ?_ rows
    rw [Zonotope.materialise_eq]
    exact GraphNet.aux_plusPoint (Zonotope.containsAt_mtimes L.W (hE L.src).2) L.b
  have hr₀ : rows ≤ Z₀.h := by
    show rows ≤ _ + (rows - _)
    omega
  -- 2. the residuals, one by one
  have hfold : ∀ (rs : List (GraphResidual 𝕋 Γ m)) (Z : Zonotope (Vec 𝕋 m)) (y : Vec ℝ m),
      rows ≤ Z.h → Z.ContainsAt (fun j => β j.1) y →
      rows ≤ (rs.foldl (fun Z r =>
        (GraphNet.step_addRows Z (Zonotope.mtimes r.R (E r.src))).materialise) Z).h ∧
      (rs.foldl (fun Z r =>
        (GraphNet.step_addRows Z (Zonotope.mtimes r.R (E r.src))).materialise) Z).ContainsAt
        (fun j => β j.1)
        (fun i => y i + (rs.map fun r => ∑ j, toReal (r.R i j) * e r.src j).sum) := by
    -- by induction on the residuals, each by `aux_addRows`
    intro rs
    induction rs with
    | nil =>
      intro Z y hr h
      rw [List.foldl_nil]
      refine ⟨hr, ?_⟩
      convert h using 1
      funext i
      simp only [List.map_nil, List.sum_nil, add_zero]
    | cons r rs ih =>
      intro Z y hr h
      have hle : (Zonotope.mtimes r.R (E r.src)).h ≤ Z.h := ((hE r.src).1).trans hr
      have h' := GraphNet.aux_addRows hle hβ h (Zonotope.containsAt_mtimes r.R (hE r.src).2)
      rw [← Zonotope.materialise_eq (GraphNet.step_addRows Z _)] at h'
      obtain ⟨hr', hmem⟩ := ih _ _ (show rows ≤ (GraphNet.step_addRows Z
        (Zonotope.mtimes r.R (E r.src))).materialise.h from hr) h'
      -- the next residual's image adds to the sum
      rw [List.foldl_cons]
      refine ⟨hr', ?_⟩
      convert hmem using 1
      funext i
      simp only [Pi.add_apply, List.map_cons, List.sum_cons]
      rw [add_assoc]
      rfl
  -- 3. the sum is the layer's input
  obtain ⟨hr, hmem⟩ := hfold L.residuals Z₀ _ hr₀ h₀
  refine ⟨hr, ?_⟩
  have hpre : (L.toReal a).preact e = fun i => (toRealMat L.W *ᵥ e L.src + toRealVec L.b) i
      + (L.residuals.map fun r => ∑ j, toReal (r.R i j) * e r.src j).sum := by
    funext i
    simp only [Real.GraphLayer.preact, GraphLayer.toReal, List.map_map]
    rfl
  rw [hpre]
  exact hmem

/-- From the outputs `E` at `β`, the rest of the network encloses the rest of the exact one. -/
private theorem GraphNet.aux_run {Γ : List ℕ} {k : ℕ} {F : GraphNet 𝕋 Γ k}
    {R : Real.GraphNet Γ k} (h : F.Images R) : -- --- CONCL ---
    ∀ (E : GraphEnv 𝒵[𝕋] Γ) (e : GraphEnv (Vec ℝ) Γ) (β : ℕ → ℝ)
      (rows : ℕ), (∀ j, |β j| ≤ 1) →
      (∀ i, (E i).h ≤ rows ∧ (E i).ContainsAt (fun j => β j.1) (e i)) →
      R.eval e ∈ (F.step_run E rows).toSet := by -- --- PROOF ---
  induction h with
  | done =>
    intro E e β rows _ hE
    exact Zonotope.mem_toSet_iff_containsAt.mpr ⟨_, (hE _).2⟩
  | @layer Γ' m k' L rest a R ha _ ih =>
    intro E e β rows hβ hE
    obtain ⟨hrows, hlin⟩ := GraphNet.aux_linear L a hβ hE
    obtain ⟨β', hβ', hag, hh, hact⟩ := GraphNet.aux_activate ha hβ hlin
    refine ih _ _ β' _ hβ' fun i => ?_
    rcases i with ⟨_ | i, hi⟩
    · exact ⟨le_rfl, hact⟩
    · have hEi := hE ⟨i, Nat.lt_of_succ_lt_succ hi⟩
      exact ⟨(hEi.1.trans hrows).trans hh, GraphNet.aux_containsAt_congr
        (fun j hj => hag j (lt_of_lt_of_le hj (hEi.1.trans hrows))) hEi.2⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem GraphNet.evaluateGraph_encloses {k : ℕ} {F : GraphNet 𝕋 [n] k} {R : Real.GraphNet [n] k}
    (h : F.Images R) (X : Zonotope (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : x ∈ X.toSet) : -- --- CONCL ---
    R.eval (GraphEnv.cons x fun i => i.elim0) ∈ (F.evaluateGraph X).toSet := by -- --- PROOF ---
  obtain ⟨γ, hγ⟩ := Zonotope.mem_toSet_iff_containsAt.mp hx
  -- the input's weights, zero beyond its generators
  let β : ℕ → ℝ := fun j => if hj : j < X.h then γ ⟨j, hj⟩ else 0
  have hβ : ∀ j, |β j| ≤ 1 := fun j => by
    simp only [β]
    split_ifs
    · exact hγ.1 _
    · simp
  have hX : X.ContainsAt (fun j => β j.1) x := by
    have e : (fun j : Fin X.h => β j.1) = γ := funext fun j => by simp [β, j.2]
    rw [e]
    exact hγ
  refine GraphNet.aux_run h _ _ β X.h hβ fun i => ?_
  rcases i with ⟨_ | i, hi⟩
  · exact ⟨le_rfl, hX⟩
  · exact absurd hi (by simp)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
