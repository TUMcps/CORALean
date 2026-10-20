module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Rescale
public import CORALean.ContSet.ConPolyZono.Float.Theorems.GetSubsetPointOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# The float `rescale` encloses the constrained polynomial zonotope

The exact layer's `rescale_exact` follows a factor vector through the fold of `getSubset` steps.
The same invariant holds here, one factor vector at a time, by `getSubset_point_outer`: the float
set after `t` steps meets its constraint at `a`, and its generator sum at `a` plus a point of its
error box is the original's at the substituted vector plus the original error.

A factor vector of the original that satisfies the constraints lies in the contracted box, so it
is `cen + rad·δ` for a `δ` in `[-1,1]ᵖ`. Outer: the exact `rescale_exact` is an equality; this
needs of the contractor only that it keep every solution.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `contract` – contractor on the factor box

## Hypotheses
* `hkeep` – contractor keeps every factor vector satisfying the constraint

## Conclusion
* the set is contained in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The factor vector after the first `t` factors have been sent to `cen ± rad`. -/
def ConPolyZono.aux_rescaleSub (cen rad : ℕ → 𝕋) (t : ℕ) (a : ℕ → ℝ) : ℕ → ℝ :=
  fun k => if k < t then toReal (cen k) + toReal (rad k) * a k else a k

/-- What `t` steps of `rescaleStep` leave: the factor counts, the center and the independent
block, and, at every factor vector in `[-1,1]ᵖ` whose substitution is in `[-1,1]ᵖ` and meets
the original constraint, the constraint and the generator sum up to the error boxes. -/
def ConPolyZono.aux_RescaleInv (cPZ acc : ConPolyZono 𝕋 (Vec 𝕋 n)) (cen rad : ℕ → 𝕋)
    (t : ℕ) : Prop :=
  acc.p = cPZ.p ∧ acc.qI = cPZ.qI ∧ acc.c = cPZ.c
  ∧ (∀ (β : ℕ → ℝ) (i : Fin n), ∑ j : Fin acc.qI, toReal (acc.GI j i) * β j
      = ∑ j : Fin cPZ.qI, toReal (cPZ.GI j i) * β j)
  ∧ ∀ a : ℕ → ℝ, (∀ k, k < cPZ.p → |a k| ≤ 1)
    → (∀ k, k < cPZ.p → |ConPolyZono.aux_rescaleSub cen rad t a k| ≤ 1)
    → (fun k : Fin cPZ.p => ConPolyZono.aux_rescaleSub cen rad t a k) ∈ cPZ.cons.construct
    → (fun k : Fin acc.p => a k) ∈ acc.cons.construct
      ∧ ∀ e ∈ cPZ.I_error.construct, ∃ e' ∈ acc.I_error.construct, ∀ i,
        (∑ l, toReal (acc.G l i) * Real.PolyZonotope.monomial acc.E (fun k : Fin acc.p => a k) l)
            + e' i
          = (∑ l, toReal (cPZ.G l i) * Real.PolyZonotope.monomial cPZ.E
              (fun k : Fin cPZ.p => ConPolyZono.aux_rescaleSub cen rad t a k) l) + e i

theorem ConPolyZono.aux_rescaleSub_succ (cen rad : ℕ → 𝕋) (t : ℕ) (a : ℕ → ℝ) :
    ConPolyZono.aux_rescaleSub cen rad (t + 1) a
      = ConPolyZono.aux_rescaleSub cen rad t
          (Function.update a t (toReal (cen t) + toReal (rad t) * a t)) := by -- --- PROOF ---
  -- compare the two sides at `k` below, at, and above `t`
  funext k
  simp only [ConPolyZono.aux_rescaleSub]
  rcases lt_trichotomy k t with hk | hk | hk
  · rw [if_pos (by omega), if_pos hk, Function.update_of_ne (by omega)]
  · subst hk
    rw [if_pos (by omega), if_neg (by omega), Function.update_self]
  · rw [if_neg (by omega), if_neg (by omega), Function.update_of_ne (by omega)]

theorem ConPolyZono.aux_fin_update {m t : ℕ} (h : t < m) (a : ℕ → ℝ) (y : ℝ) :
    (fun k : Fin m => Function.update a t y (k : ℕ))
      = Function.update (fun k : Fin m => a k) ⟨t, h⟩ y := by -- --- PROOF ---
  -- the coordinate `t` is the updated one, the others are read off `a`
  funext k
  by_cases hk : k = ⟨t, h⟩
  · subst hk; simp
  · rw [Function.update_of_ne hk, Function.update_of_ne]
    intro h'
    exact hk (Fin.ext h')

theorem ConPolyZono.aux_rescaleInv_zero (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (cen rad : ℕ → 𝕋) :
    ConPolyZono.aux_RescaleInv cPZ cPZ cen rad 0 := by -- --- PROOF ---
  -- nothing has been substituted yet: the substitution is the identity, the error box the same
  refine ⟨rfl, rfl, rfl, fun _ _ => rfl, fun a _ _ hs => ?_⟩
  have hid : (fun k : Fin cPZ.p => ConPolyZono.aux_rescaleSub cen rad 0 a k)
      = fun k : Fin cPZ.p => a k := by
    funext k
    simp [ConPolyZono.aux_rescaleSub]
  rw [hid] at hs
  exact ⟨hs, fun e he => ⟨e, he, fun i => by rw [hid]⟩⟩

theorem ConPolyZono.aux_rescaleInv_succ (cPZ acc : ConPolyZono 𝕋 (Vec 𝕋 n))
    (cen rad : ℕ → 𝕋) (t : ℕ)
    (ht : t < cPZ.p) (hinv : ConPolyZono.aux_RescaleInv cPZ acc cen rad t) : -- --- CONCL ---
    ConPolyZono.aux_RescaleInv cPZ (ConPolyZono.rescaleStep cen rad acc t) cen rad
      (t + 1) := by -- --- PROOF ---
  obtain ⟨hp, hq, hc, hGI, hpt⟩ := hinv
  have h : t < acc.p := hp ▸ ht
  unfold ConPolyZono.rescaleStep
  rw [dif_pos h]
  -- the counts, the center and the independent block are untouched
  refine ⟨hp, hq, hc, fun β i => hGI β i, fun a ha hb hs => ?_⟩
  -- the vector the previous set is read at: factor `t` sent to `cen ± rad`
  have hsub := ConPolyZono.aux_rescaleSub_succ cen rad t a
  have ha' : ∀ k, k < cPZ.p →
      |Function.update a t (toReal (cen t) + toReal (rad t) * a t) k| ≤ 1 := by
    intro k hk
    by_cases hkt : k = t
    · subst hkt
      have := hb k hk
      rw [ConPolyZono.aux_rescaleSub, if_pos (Nat.lt_succ_self k)] at this
      rw [Function.update_self]
      exact this
    · rw [Function.update_of_ne hkt]
      exact ha k hk
  rw [hsub] at hb hs
  obtain ⟨hsat', hpt'⟩ := hpt _ ha' hb hs
  rw [ConPolyZono.aux_fin_update h] at hsat'
  -- one `getSubset` step at the vector itself
  have key := ConPolyZono.getSubset_point_outer acc ⟨t, h⟩ (cen t) (rad t) (fun k => a k)
    (fun k => ha k (hp ▸ k.2)) hsat'
  refine ⟨key.1, fun e he => ?_⟩
  obtain ⟨e₁, he₁, h₁⟩ := hpt' e he
  obtain ⟨e', he', h₂⟩ := key.2 e₁ he₁
  refine ⟨e', he', fun i => ?_⟩
  have h₁i := h₁ i
  rw [ConPolyZono.aux_fin_update h] at h₁i
  refine (h₂ i).trans ?_
  rw [hsub]
  exact h₁i

theorem ConPolyZono.aux_rescaleInv_fold (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (cen rad : ℕ → 𝕋) (t : ℕ)
    (ht : t ≤ cPZ.p) :
    ConPolyZono.aux_RescaleInv cPZ ((List.range t).foldl (ConPolyZono.rescaleStep cen rad) cPZ)
      cen rad t := by -- --- PROOF ---
  induction t with
  | zero => exact ConPolyZono.aux_rescaleInv_zero cPZ cen rad
  | succ t ih =>
    -- the `t + 1`-st step is `rescaleStep` at `t`
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact ConPolyZono.aux_rescaleInv_succ cPZ _ cen rad t (by omega) (ih (by omega))

/-- The rounded midpoint of `[lo, hi]`, with the radius rounded up from it to both ends,
covers the interval. -/
theorem ConPolyZono.aux_cover (lo hi : 𝕋) (v : ℝ) (h : toReal lo ≤ v ∧ v ≤ toReal hi) :
    |v - toReal (half (addDown hi lo))| ≤
      toReal (maximum (subUp hi (half (addDown hi lo)))
        (subUp (half (addDown hi lo)) lo)) := by -- --- PROOF ---
  have h1 := sub_le_subUp hi (half (addDown hi lo))
  have h2 := sub_le_subUp (half (addDown hi lo)) lo
  rw [toReal_maximum]
  have h4 := le_max_left (toReal (subUp hi (half (addDown hi lo))))
    (toReal (subUp (half (addDown hi lo)) lo))
  have h5 := le_max_right (toReal (subUp hi (half (addDown hi lo))))
    (toReal (subUp (half (addDown hi lo)) lo))
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- Any midpoints and radii whose boxes cover every factor vector of `[-1,1]ᵖ` satisfying the
constraints: the fold onto them encloses the set. -/
theorem ConPolyZono.aux_rescale_outer_of_cover (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (cen rad : ℕ → 𝕋)
    (hcov : ∀ x : Fin cPZ.p → ℝ, (∀ k, |x k| ≤ 1) → x ∈ cPZ.cons.construct →
      ∀ k : Fin cPZ.p, |x k - toReal (cen k)| ≤ toReal (rad k)) : -- --- CONCL ---
    cPZ.construct ⊆ ConPolyZono.construct
      ((List.range cPZ.p).foldl (ConPolyZono.rescaleStep cen rad) cPZ) := by -- --- PROOF ---
  rintro _ ⟨y, hy, e, he, rfl⟩
  obtain ⟨x, β, hx, hβ, hs, hy⟩ := ConPolyZono.mem_nominalSet_iff.mp hy
  obtain ⟨hp, hq, hc, hGI, hpt⟩ := ConPolyZono.aux_rescaleInv_fold cPZ cen rad cPZ.p le_rfl
  set acc := (List.range cPZ.p).foldl (ConPolyZono.rescaleStep cen rad) cPZ with hacc
  have hdev := hcov x hx hs
  -- the rescaled factors, `0` where the box is a point
  set δ : ℕ → ℝ := fun r => if h : r < cPZ.p then
      (if toReal (rad r) = 0 then 0 else (x ⟨r, h⟩ - toReal (cen r)) / toReal (rad r))
    else 0 with hδdef
  have hδ : ∀ k, k < cPZ.p → |δ k| ≤ 1 := by
    intro k hk'
    simp only [hδdef, dif_pos hk']
    split_ifs with h0
    · simp
    · have hd := hdev ⟨k, hk'⟩
      have hpos : 0 < toReal (rad k) :=
        lt_of_le_of_ne (le_trans (abs_nonneg _) hd) (Ne.symm h0)
      rw [abs_div, abs_of_pos hpos, div_le_one hpos]
      exact hd
  -- and they map back onto the original's
  have hsubx : (fun k : Fin cPZ.p => ConPolyZono.aux_rescaleSub cen rad cPZ.p δ k) = x := by
    funext k
    have hd := hdev k
    simp only [ConPolyZono.aux_rescaleSub, if_pos k.2, hδdef, dif_pos k.2]
    split_ifs with h0
    · rw [h0] at hd
      have : x k - toReal (cen k) = 0 := abs_nonpos_iff.mp hd
      rw [h0]; linarith
    · field_simp
      ring
  have hb : ∀ k, k < cPZ.p → |ConPolyZono.aux_rescaleSub cen rad cPZ.p δ k| ≤ 1 := by
    intro k hk'
    have := congrFun hsubx ⟨k, hk'⟩
    simp only at this
    rw [this]
    exact hx _
  obtain ⟨hsat, hpt'⟩ := hpt δ hδ hb (by rw [hsubx]; exact hs)
  obtain ⟨e', he', heq⟩ := hpt' e he
  -- the coefficients of the independent block, read on `ℕ`
  set βN : ℕ → ℝ := fun j => if h : j < cPZ.qI then β ⟨j, h⟩ else 0 with hβNdef
  have hβN : ∀ i : Fin n, ∑ j : Fin cPZ.qI, toReal (cPZ.GI j i) * βN j
      = ∑ j : Fin cPZ.qI, toReal (cPZ.GI j i) * β j := fun i =>
    Finset.sum_congr rfl fun j _ => by simp [hβNdef, j.2]
  refine ⟨fun i => toReal (acc.c i)
      + (∑ l, toReal (acc.G l i) * Real.PolyZonotope.monomial acc.E (fun k => δ k) l)
      + ∑ j : Fin acc.qI, toReal (acc.GI j i) * βN j,
    ConPolyZono.mem_nominalSet_iff.mpr ⟨fun k => δ k, fun j => βN j,
      fun k => hδ k (hp ▸ k.2), fun j => ?_, hsat, fun _ => rfl⟩, e', he', ?_⟩
  · -- the coefficients stay in `[-1, 1]`
    have hj : (j : ℕ) < cPZ.qI := hq ▸ j.2
    show |(if h : (j : ℕ) < cPZ.qI then β ⟨j, h⟩ else 0)| ≤ 1
    rw [dif_pos hj]
    exact hβ _
  · -- the point: the invariant at `δ`, the center and the independent block unchanged
    funext i
    have hi := heq i
    rw [hsubx] at hi
    show toReal (acc.c i)
        + (∑ l, toReal (acc.G l i) * Real.PolyZonotope.monomial acc.E (fun k => δ k) l)
        + ∑ j : Fin acc.qI, toReal (acc.GI j i) * βN j + e' i = y i + e i
    rw [hy i, hc, hGI βN i, hβN i]
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- `rescale` encloses the set, for any contractor of the constraints that keeps every factor
vector of the unit box satisfying them. -/
theorem ConPolyZono.rescale_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (contract : Interval (Vec 𝕋 cPZ.p) → Interval (Vec 𝕋 cPZ.p))
    (hkeep : ∀ x : Vec ℝ cPZ.p,
        x ∈ ((Interval.unit cPZ.p : Interval (Vec 𝕋 cPZ.p))).construct → x ∈ cPZ.cons.construct →
      x ∈ (contract ((Interval.unit cPZ.p : Interval (Vec 𝕋 cPZ.p)))).construct) : -- --- CONCL ---
    cPZ.construct ⊆ (cPZ.rescale contract).construct := by -- --- PROOF ---
  unfold ConPolyZono.rescale
  dsimp only
  refine ConPolyZono.aux_rescale_outer_of_cover cPZ _ _ (fun x hx hs k => ?_)
  simp only [Fin.is_lt, dif_pos, Fin.eta]
  refine ConPolyZono.aux_cover _ _ _ ?_
  -- the unit box, read as reals
  have hunit : x ∈ ((Interval.unit cPZ.p : Interval (Vec 𝕋 cPZ.p))).construct := fun i => by
    show toReal (neg one) ≤ x i ∧ x i ≤ toReal one
    rw [toReal_neg, toReal_one]
    exact abs_le.mp (hx i)
  by_cases hA : cPZ.cons.m = 0 ∨ cPZ.cons.q = 0
  · -- empty `A`: CORA does not contract, the box stays `[-1,1]ᵖ`
    rw [if_pos hA]
    exact hunit k
  · -- the contractor keeps every solution in the unit box
    rw [if_neg hA]
    exact hkeep x hunit hs k

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
