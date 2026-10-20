module

public import Mathlib.Analysis.Calculus.Darboux
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Comp

@[expose] public section

/-!
# Moving one coordinate at a time through a box

[1, Thm. 1]'s mean-value arguments move from the center of a box to a point of it one coordinate
at a time, coordinate `i` varied with every coordinate before it at the center, and bound each move
by `∂ᵢf` on that *path set*. Three facts: the moves change `f` by at most `Σ Uᵢ rᵢ` when
`|∂ᵢf| ≤ Uᵢ` on the path sets; some point raises `f` by at least `Σ Lᵢ rᵢ` when `|∂ᵢf| ≥ Lᵢ` there
(each move's direction from the sign of `∂ᵢf`, constant along a line by Darboux's theorem); and for
any start and targets the gains of the single moves add up (`le_of_coord_gain`), which a Kaucher
mean-value extension needs. `∂ᵢf y` is `fderiv ℝ f y (Pi.single i 1)`; `f` is differentiable, which
is all the arguments use ([1] assumes `C¹`).

## Inputs
* `g` – function of one variable
* `g'` – its derivative
* `c` – center of the interval
* `r` – radius of the interval
* `L` – lower bound on the derivative's absolute value

## Hypotheses
* `hr` – radius nonnegative
* `hg` – `g'` is the derivative of `g` on the interval
* `hL` – the derivative is at least `L` in absolute value on the interval

## Conclusion
* some point of the interval has `g` at least `g c` plus `L` times the radius

## References

* [1] E. Goubault and S. Putot. "Robust Under-Approximations and Application to
      Reachability of Non-Linear Control Systems With Disturbances". IEEE Control Systems
      Letters, 4(4):928-933, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Splitting the threshold sum at `k`: the coordinates from `k` on are coordinate `k` and
those from `k + 1` on. -/
theorem aux_sum_ite_succ (L : Fin m → ℝ) (k : ℕ) (hk : k < m) : -- --- CONCL ---
    ∑ j : Fin m, (if k ≤ j.val then L j else 0)
      = (∑ j : Fin m, if k + 1 ≤ j.val then L j else 0) + L ⟨k, hk⟩ := by -- --- PROOF ---
  have h : ∀ j : Fin m, (if k ≤ j.val then L j else 0)
      = (if k + 1 ≤ j.val then L j else 0) + (if j = ⟨k, hk⟩ then L j else 0) := by
    intro j
    by_cases h1 : k + 1 ≤ j.val
    · have : j ≠ ⟨k, hk⟩ := fun h => by rw [h] at h1; exact absurd h1 (by simp)
      simp [h1, this, show k ≤ j.val by omega]
    · by_cases h2 : j = ⟨k, hk⟩
      · subst h2; simp
      · have : ¬ k ≤ j.val := fun h => h2 (Fin.ext (by simp only; omega))
        simp [h1, h2, this]
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- The coordinate line through `p` stays in the box, and its derivative is `∂ᵢf`. -/
theorem hasDerivAt_comp_update {f : (Fin m → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (p : Fin m → ℝ) (i : Fin m) (t : ℝ) :
    HasDerivAt (fun s => f (Function.update p i s))
      (fderiv ℝ f (Function.update p i t) (Pi.single i 1)) t :=
  (hf _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update p i t)

/-- Points of a box with one coordinate replaced inside its bounds stay in the box. -/
theorem update_mem_Icc {lo hi p : Fin m → ℝ} (hp : p ∈ Icc lo hi) (i : Fin m) {t : ℝ}
    (ht : t ∈ Icc (lo i) (hi i)) : -- --- CONCL ---
    Function.update p i t ∈ Icc lo hi := by -- --- PROOF ---
  refine ⟨fun j => ?_, fun j => ?_⟩ <;> by_cases h : j = i
  · subst h; simpa using ht.1
  · simpa [Function.update_of_ne h] using hp.1 j
  · subst h; simpa using ht.2
  · simpa [Function.update_of_ne h] using hp.2 j


-- =======================================  MAIN THEOREM  ======================================= --

/-- One dimension: `|g'| ≥ L` on `[c - r, c + r]` puts a point there where `g` is at least
`g c + L r`, on whichever side `g'`'s constant sign points to. -/
theorem exists_ge_add_of_abs_deriv_ge {g g' : ℝ → ℝ} {c r L : ℝ} (hr : 0 ≤ r)
    (hg : ∀ t ∈ Icc (c - r) (c + r), HasDerivAt g (g' t) t)
    (hL : ∀ t ∈ Icc (c - r) (c + r), L ≤ |g' t|) : -- --- CONCL ---
    ∃ t ∈ Icc (c - r) (c + r), g c + L * r ≤ g t := by -- --- PROOF ---
  have hc : c ∈ Icc (c - r) (c + r) := ⟨by linarith, by linarith⟩
  by_cases hLr : L * r ≤ 0
  · exact ⟨c, hc, by linarith⟩
  have hr0 : 0 < r := lt_of_le_of_ne hr fun h => hLr (by rw [← h, mul_zero])
  have hL0 : 0 < L := by by_contra h; exact hLr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hr)
  have hcont : ContinuousOn g (Icc (c - r) (c + r)) := fun t ht =>
    (hg t ht).continuousAt.continuousWithinAt
  -- Darboux: `g'` takes no value `0` on the interval, so it keeps one sign
  have hsign : (∀ t ∈ Icc (c - r) (c + r), 0 < g' t) ∨ ∀ t ∈ Icc (c - r) (c + r), g' t < 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨a, ha, hga⟩, ⟨b, hb, hgb⟩⟩ := hcon
    have hord := (ordConnected_Icc (a := c - r) (b := c + r)).image_hasDerivWithinAt
      (fun t ht => (hg t ht).hasDerivWithinAt)
    obtain ⟨z, hz, hz0⟩ := hord.out (mem_image_of_mem g' ha) (mem_image_of_mem g' hb)
      ⟨hga, hgb⟩
    have := hL z hz
    rw [hz0, abs_zero] at this
    linarith
  rcases hsign with hpos | hneg
  -- increasing: move up to `c + r`
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope g g' (by linarith : c < c + r)
      (hcont.mono (Icc_subset_Icc (by linarith) le_rfl))
      (fun t ht => hg t ⟨by linarith [ht.1], ht.2.le⟩)
    have hξ' : ξ ∈ Icc (c - r) (c + r) := ⟨by linarith [hξ.1], hξ.2.le⟩
    have hge : L ≤ g' ξ := (abs_of_pos (hpos ξ hξ')) ▸ hL ξ hξ'
    refine ⟨c + r, ⟨by linarith, le_rfl⟩, ?_⟩
    rw [add_sub_cancel_left, eq_div_iff hr0.ne'] at hslope
    nlinarith
  -- decreasing: move down to `c - r`
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope g g' (by linarith : c - r < c)
      (hcont.mono (Icc_subset_Icc le_rfl (by linarith)))
      (fun t ht => hg t ⟨ht.1.le, by linarith [ht.2]⟩)
    have hξ' : ξ ∈ Icc (c - r) (c + r) := ⟨hξ.1.le, by linarith [hξ.2]⟩
    have hge : L ≤ -g' ξ := (abs_of_neg (hneg ξ hξ')) ▸ hL ξ hξ'
    refine ⟨c - r, ⟨le_rfl, by linarith⟩, ?_⟩
    rw [sub_sub_cancel, eq_div_iff hr0.ne'] at hslope
    nlinarith

/-- [1, Thm. 1]'s inner argument: with `|∂ᵢf| ≥ Lᵢ` on the `i`-th path set, some point
of the box raises `f` from the center by at least `Σ Lᵢ rᵢ`. -/
theorem exists_ge_add_sum_of_abs_partial_ge {f : (Fin m → ℝ) → ℝ} (hf : Differentiable ℝ f)
    {lo hi : Fin m → ℝ} (hlh : lo ≤ hi) (L : Fin m → ℝ)
    (hL : ∀ i, ∀ y ∈ Icc lo hi, (∀ j, j < i → y j = (lo j + hi j) / 2) →
      L i ≤ |fderiv ℝ f y (Pi.single i 1)|) : -- --- CONCL ---
    ∃ p ∈ Icc lo hi, f (fun i => (lo i + hi i) / 2)
      + ∑ i, L i * ((hi i - lo i) / 2) ≤ f p := by -- --- PROOF ---
  set c : Fin m → ℝ := fun i => (lo i + hi i) / 2 with hc
  have hcmem : c ∈ Icc lo hi := ⟨fun i => by simp only [hc]; linarith [hlh i],
    fun i => by simp only [hc]; linarith [hlh i]⟩
  -- the coordinates from `m - d` on have moved, the others are still at the center
  have key : ∀ d ≤ m, ∃ p ∈ Icc lo hi, (∀ j : Fin m, j.val < m - d → p j = c j) ∧
      f c + ∑ j : Fin m, (if m - d ≤ j.val then L j * ((hi j - lo j) / 2) else 0) ≤ f p := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨c, hcmem, fun _ _ => rfl, ?_⟩
      rw [Finset.sum_eq_zero fun j _ => if_neg (not_le.mpr (by simp))]
      simp
    | succ d ih =>
      intro hd
      obtain ⟨p, hp, hpc, hfp⟩ := ih (by omega)
      set k := m - (d + 1) with hk
      have hkm : k < m := by omega
      set i : Fin m := ⟨k, hkm⟩
      have hpi : p i = c i := hpc i (by simp [i]; omega)
      -- vary coordinate `k` along `[lo k, hi k] = [c k - r k, c k + r k]`
      have hIcc : Icc (c i - (hi i - lo i) / 2) (c i + (hi i - lo i) / 2) = Icc (lo i) (hi i) := by
        congr 1 <;> simp only [hc] <;> ring
      obtain ⟨t, ht, hgt⟩ := exists_ge_add_of_abs_deriv_ge (c := c i) (r := (hi i - lo i) / 2)
        (L := L i) (by linarith [hlh i]) (fun t _ => hasDerivAt_comp_update hf p i t)
        (fun t ht => hL i _ (update_mem_Icc hp i (hIcc ▸ ht)) fun j hj => by
          rw [Function.update_of_ne (Fin.ne_of_lt hj)]
          exact hpc j (by have := Fin.lt_def.mp hj; simp [i] at this; omega))
      refine ⟨Function.update p i t, update_mem_Icc hp i (hIcc ▸ ht), fun j hj => ?_, ?_⟩
      · have hji : j ≠ i := fun h => by rw [h] at hj; simp [i] at hj
        rw [Function.update_of_ne hji]
        exact hpc j (by omega)
      · rw [← hpi, Function.update_eq_self] at hgt
        rw [show m - d = k + 1 by omega] at hfp
        rw [aux_sum_ite_succ _ k hkm]
        linarith
  obtain ⟨p, hp, -, hfp⟩ := key m le_rfl
  exact ⟨p, hp, by simpa using hfp⟩

/-- [1, Thm. 1]'s outer argument: with `|∂ᵢf| ≤ Uᵢ` on the `i`-th path set, `f` moves from
the center by at most `Σ Uᵢ rᵢ` anywhere in the box. -/
theorem abs_sub_le_sum_of_abs_partial_le {f : (Fin m → ℝ) → ℝ} (hf : Differentiable ℝ f)
    {lo hi : Fin m → ℝ} (U : Fin m → ℝ)
    (hU : ∀ i, ∀ y ∈ Icc lo hi, (∀ j, j < i → y j = (lo j + hi j) / 2) →
      |fderiv ℝ f y (Pi.single i 1)| ≤ U i) {x : Fin m → ℝ} (hx : x ∈ Icc lo hi) : -- --- CONCL ---
    |f x - f (fun i => (lo i + hi i) / 2)| ≤ ∑ i, U i * ((hi i - lo i) / 2) := by -- --- PROOF ---
  set c : Fin m → ℝ := fun i => (lo i + hi i) / 2 with hc
  -- `q k`: the first `k` coordinates at the center, the rest at `x`
  let q : ℕ → Fin m → ℝ := fun k j => if j.val < k then c j else x j
  have hq : ∀ k, q k ∈ Icc lo hi := fun k => ⟨fun j => by
      by_cases h : j.val < k <;> simp only [q, h, if_true, if_false, hc] <;>
        linarith [hx.1 j, hx.2 j],
    fun j => by
      by_cases h : j.val < k <;> simp only [q, h, if_true, if_false, hc] <;>
        linarith [hx.1 j, hx.2 j]⟩
  -- moving the first `k` coordinates changes `f` by at most their terms
  have key : ∀ k ≤ m, |f (q k) - f x|
      ≤ ∑ j : Fin m, (if j.val < k then U j * ((hi j - lo j) / 2) else 0) := by
    intro k
    induction k with
    | zero => intro _; simp [q]
    | succ k ih =>
      intro hk
      set i : Fin m := ⟨k, by omega⟩
      -- one more coordinate at the center is one update
      have hstep : q (k + 1) = Function.update (q k) i (c i) := by
        funext j
        by_cases h : j = i
        · subst h; simp [q, i]
        · rw [Function.update_of_ne h]
          have : j.val ≠ k := fun h' => h (Fin.ext h')
          by_cases h' : j.val < k
          · simp [q, h', show j.val < k + 1 by omega]
          · simp [q, h', show ¬ j.val < k + 1 by omega]
      have hqi : q k i = x i := by simp [q, i]
      have hci : c i ∈ Icc (lo i) (hi i) := by
        simp only [hc]; constructor <;> linarith [hx.1 i, hx.2 i]
      -- the move of coordinate `k`, from `x k` to `c k`, along its path set
      have hmove : |f (q (k + 1)) - f (q k)| ≤ U i * ((hi i - lo i) / 2) := by
        have hseg := (convex_Icc (lo i) (hi i)).norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun s => f (Function.update (q k) i s))
          (fun t _ => (hasDerivAt_comp_update hf (q k) i t).hasDerivWithinAt)
          (fun t ht => by
            rw [Real.norm_eq_abs]
            refine hU i _ (update_mem_Icc (hq k) i ht) fun j hj => ?_
            rw [Function.update_of_ne (Fin.ne_of_lt hj)]
            have : j.val < k := Fin.lt_def.mp hj
            simp [q, this, hc])
          ⟨hx.1 i, hx.2 i⟩ hci
        have h1 : Function.update (q k) i (x i) = q k := by rw [← hqi, Function.update_eq_self]
        simp only [h1, ← hstep, Real.norm_eq_abs] at hseg
        -- `|∂ᵢf| ≤ Uᵢ` somewhere, so `Uᵢ ≥ 0`, and `|cᵢ - xᵢ| ≤ rᵢ`
        have hU0 : 0 ≤ U i := (abs_nonneg _).trans (hU i _ (hq (k + 1)) fun j hj => by
          have : j.val < k := Fin.lt_def.mp hj
          simp [q, show j.val < k + 1 by omega, hc])
        refine hseg.trans (mul_le_mul_of_nonneg_left ?_ hU0)
        simp only [hc]
        rw [abs_le]
        constructor <;> linarith [hx.1 i, hx.2 i]
      -- the sum gains coordinate `k`'s term
      have hsum : ∑ j : Fin m, (if j.val < k + 1 then U j * ((hi j - lo j) / 2) else 0)
          = (∑ j : Fin m, if j.val < k then U j * ((hi j - lo j) / 2) else 0)
            + U i * ((hi i - lo i) / 2) := by
        have h : ∀ j : Fin m, (if j.val < k + 1 then U j * ((hi j - lo j) / 2) else 0)
            = (if j.val < k then U j * ((hi j - lo j) / 2) else 0)
              + (if j = i then U j * ((hi j - lo j) / 2) else 0) := by
          intro j
          by_cases h : j = i
          · subst h; simp [i]
          · have : j.val ≠ k := fun h' => h (Fin.ext h')
            by_cases h' : j.val < k
            · simp [h', h, show j.val < k + 1 by omega]
            · simp [h', h, show ¬ j.val < k + 1 by omega]
        rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
      -- triangle inequality through `q k`
      rw [hsum]
      calc |f (q (k + 1)) - f x| ≤ |f (q (k + 1)) - f (q k)| + |f (q k) - f x| :=
            abs_sub_le _ _ _
        _ ≤ _ := by linarith [ih (by omega)]
  -- all `m` coordinates at the center is the center
  have hqm : q m = c := funext fun j => by simp [q, j.is_lt]
  have := key m le_rfl
  rw [hqm, abs_sub_comm] at this
  simpa using this

/-- Moving every coordinate from `x₀` to its target `t`, each move gaining at least `γᵢ`
from wherever the others are: `f t ≥ f x₀ + Σ γᵢ`. -/
theorem le_of_coord_gain {f : (Fin m → ℝ) → ℝ} {lo hi : Fin m → ℝ} {x₀ t : Fin m → ℝ}
    (hx₀ : x₀ ∈ Icc lo hi) (ht : t ∈ Icc lo hi) (γ : Fin m → ℝ)
    (hγ : ∀ i, ∀ p ∈ Icc lo hi, f (Function.update p i (x₀ i)) + γ i
      ≤ f (Function.update p i (t i))) : -- --- CONCL ---
    f x₀ + ∑ i, γ i ≤ f t := by -- --- PROOF ---
  -- `p k`: the first `k` coordinates at the target, the rest at `x₀`
  let p : ℕ → Fin m → ℝ := fun k j => if j.val < k then t j else x₀ j
  have hp : ∀ k, p k ∈ Icc lo hi := fun k => ⟨fun j => by
      by_cases h : j.val < k <;> simp only [p, h, if_true, if_false] <;> first
        | exact ht.1 j | exact hx₀.1 j,
    fun j => by
      by_cases h : j.val < k <;> simp only [p, h, if_true, if_false] <;> first
        | exact ht.2 j | exact hx₀.2 j⟩
  have key : ∀ k ≤ m, f x₀ + ∑ j : Fin m, (if j.val < k then γ j else 0) ≤ f (p k) := by
    intro k
    induction k with
    | zero => intro _; simp [p]
    | succ k ih =>
      intro hk
      set i : Fin m := ⟨k, by omega⟩
      -- coordinate `k` is still at `x₀` before the move and at `t` after it
      have h0 : Function.update (p k) i (x₀ i) = p k := by
        rw [← Function.update_eq_self i (p k)]; simp [p, i]
      have h1 : Function.update (p k) i (t i) = p (k + 1) := by
        funext j
        by_cases h : j = i
        · subst h; simp [p, i]
        · rw [Function.update_of_ne h]
          have : j.val ≠ k := fun h' => h (Fin.ext h')
          by_cases h' : j.val < k
          · simp [p, h', show j.val < k + 1 by omega]
          · simp [p, h', show ¬ j.val < k + 1 by omega]
      have hstep := hγ i (p k) (hp k)
      rw [h0, h1] at hstep
      -- the sum gains coordinate `k`'s gain
      have hsum : ∑ j : Fin m, (if j.val < k + 1 then γ j else 0)
          = (∑ j : Fin m, if j.val < k then γ j else 0) + γ i := by
        have h : ∀ j : Fin m, (if j.val < k + 1 then γ j else 0)
            = (if j.val < k then γ j else 0) + (if j = i then γ j else 0) := by
          intro j
          by_cases h : j = i
          · subst h; simp [i]
          · have : j.val ≠ k := fun h' => h (Fin.ext h')
            by_cases h' : j.val < k
            · simp [h', h, show j.val < k + 1 by omega]
            · simp [h', h, show ¬ j.val < k + 1 by omega]
        rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
      rw [hsum]
      linarith [ih (by omega)]
  have hpm : p m = t := funext fun j => by simp [p, j.is_lt]
  have := key m le_rfl
  rw [hpm] at this
  simpa using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
