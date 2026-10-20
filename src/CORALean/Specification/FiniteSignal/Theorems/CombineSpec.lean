module

public import CORALean.Specification.FiniteSignal.Definitions.IsValid
public import CORALean.Specification.FiniteSignal.Operations.Combine
public import CORALean.Specification.FiniteSignal.Theorems.AtEqValueAt
public import CORALean.Specification.FiniteSignal.Theorems.Basic
public import CORALean.Specification.FiniteSignal.Theorems.ValueAtConsOfGe
public import CORALean.Specification.FiniteSignal.Theorems.CombineLoopStep
public import CORALean.Specification.FiniteSignal.Theorems.MkEqSomeIff
public import CORALean.Specification.FiniteSignal.Theorems.TimeLeDuration

@[expose] public section

/-!
# What `combine` computes

For valid signals `combine` does not throw and returns a valid signal whose duration is the
shorter one. At every time up to its end, and at the end itself if both signals end together, its
value is the operator applied to the values of the two signals. (At the end of the shorter signal,
if the longer one has a breakpoint there, the value is that of the longer signal's cell ending
there, not of the one starting there.) The loop on breakpoints is analysed first: its output is
strictly increasing in time with no two consecutive values equal.

## Inputs
* `T` – time type
* `V` – value type of the inputs
* `W` – value type of the result
* `op` – binary operator on values
* `lhs` – left signal
* `rhs` – right signal

## Hypotheses
* `hl` – the left signal is valid
* `hr` – the right signal is valid

## Conclusion
* a valid signal of the shorter duration applying the operator pointwise
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `e` is the last of the times `l`: one of them, and no time exceeds it. -/
def aux_IsLast {T : Type} [LinearOrder T] (e : T) (l : List T) : Prop := e ∈ l ∧ ∀ x ∈ l, x ≤ e

theorem aux_isLast_tail {T : Type} [LinearOrder T] (e a : T) (as : List T)
    (hs : ∀ y ∈ as, a < y) (h : aux_IsLast e (a :: as)) (hne : as ≠ []) : -- --- CONCL ---
    aux_IsLast e as := by -- --- PROOF ---
  obtain ⟨hm, hle⟩ := h
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil as hne
  refine ⟨?_, fun x hx => hle x (List.mem_cons_of_mem _ hx)⟩
  rcases List.mem_cons.mp hm with rfl | hm
  · exact absurd (hle y (List.mem_cons_of_mem _ hy)) (not_le.mpr (hs y hy))
  · exact hm

/-- With a later breakpoint or none at all, the first breakpoint's value holds. -/
theorem aux_valueAt_first {T V : Type} [LinearOrder T] (p : T × V) (q : List (T × V)) (t : T)
    (y : V) (h : t < p.1 ∨ q = []) (hy : FiniteSignal.valueAt (p :: q) t = some y) : y = p.2 := by
  rcases h with h | rfl
  · rw [FiniteSignal.valueAt_cons_of_lt p q t h] at hy; exact (Option.some.inj hy).symm
  · have := FiniteSignal.valueAt_singleton p t
    rw [this] at hy; exact (Option.some.inj hy).symm

/-- The singleton case of the loop: one of the signals is used up. -/
theorem aux_combineLoop_single {T V : Type} [LinearOrder T] (l r : T × V) (ls rs : List (T × V))
    (hL : ((l :: ls).map Prod.fst).Pairwise (· < ·))
    (hR : ((r :: rs).map Prod.fst).Pairwise (· < ·)) (eL eR t₀ : T)
    (heL : aux_IsLast eL ((l :: ls).map Prod.fst)) (heR : aux_IsLast eR ((r :: rs).map Prod.fst))
    (hmin : t₀ = min l.1 r.1) (ls' rs' : List (T × V))
    (hA1 : (ls' = ls ∧ t₀ = l.1) ∨ (ls' = l :: ls ∧ t₀ < l.1))
    (hA2 : (rs' = rs ∧ t₀ = r.1) ∨ (rs' = r :: rs ∧ t₀ < r.1))
    (hnil : ls' = [] ∨ rs' = []) : -- --- CONCL ---
    t₀ = min eL eR ∧ ∀ t x y, FiniteSignal.valueAt (l :: ls) t = some x →
      FiniteSignal.valueAt (r :: rs) t = some y → (t < eL ∧ t < eR ∨ eL = eR ∧ t = eL) →
        x = l.2 ∧ y = r.2 := by -- --- PROOF ---
  have hl1 : l.1 ≤ eL := heL.2 _ (by simp)
  have hr1 : r.1 ≤ eR := heR.2 _ (by simp)
  rw [List.map_cons, List.pairwise_cons] at hL hR
  -- the first breakpoint of each list has the last time exactly if it is alone
  have hlone : ∀ (z : T × V) (zs : List (T × V)) (e : T), (∀ y ∈ zs.map Prod.fst, z.1 < y) →
      aux_IsLast e ((z :: zs).map Prod.fst) → e = z.1 → zs = [] := by
    intro z zs e hz he hez
    by_contra hne
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil zs hne
    have hy' : y.1 ∈ (z :: zs).map Prod.fst := by
      rw [List.map_cons]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hy)
    exact absurd (he.2 y.1 hy') (not_le.mpr (hez ▸ hz y.1 (List.mem_map_of_mem hy)))
  rcases hnil with h | h
  · -- the left signal is used up
    have hls : ls = [] ∧ t₀ = l.1 := by
      rcases hA1 with ⟨h1, h2⟩ | ⟨h1, -⟩
      · exact ⟨h ▸ h1.symm, h2⟩
      · rw [h1] at h; exact absurd h (List.cons_ne_nil _ _)
    -- unpack the facts from the previous steps
    obtain ⟨rfl, h0⟩ := hls
    have heL' : eL = l.1 := by simpa using heL.1
    have hle : l.1 ≤ r.1 := calc l.1 = min l.1 r.1 := (hmin.symm.trans h0).symm
      _ ≤ r.1 := min_le_right _ _
    refine ⟨?_, fun t x y hx hy hok => ⟨?_, ?_⟩⟩
    · rw [h0, heL']; exact (min_eq_left (hle.trans hr1)).symm
    · have := FiniteSignal.valueAt_singleton l t
      rw [this] at hx; exact (Option.some.inj hx).symm
    · refine aux_valueAt_first r rs t y ?_ hy
      rcases hok with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact Or.inl (lt_of_lt_of_le (heL' ▸ h1) hle)
      · exact Or.inr (hlone r rs eR (fun y hy => hR.1 y hy) heR (le_antisymm
          (by rw [← h1, heL']; exact hle) hr1))
  · -- the right signal is used up
    -- the fact `hrs`
    have hrs : rs = [] ∧ t₀ = r.1 := by
      rcases hA2 with ⟨h1, h2⟩ | ⟨h1, -⟩
      · exact ⟨h ▸ h1.symm, h2⟩
      · rw [h1] at h; exact absurd h (List.cons_ne_nil _ _)
    obtain ⟨rfl, h0⟩ := hrs
    have heR' : eR = r.1 := by simpa using heR.1
    have hle : r.1 ≤ l.1 := calc r.1 = min l.1 r.1 := (hmin.symm.trans h0).symm
      _ ≤ l.1 := min_le_left _ _
    refine ⟨?_, fun t x y hx hy hok => ⟨?_, ?_⟩⟩
    · rw [h0, heR']; exact (min_eq_right (hle.trans hl1)).symm
    · refine aux_valueAt_first l ls t x ?_ hx
      rcases hok with ⟨-, h1⟩ | ⟨h1, h2⟩
      · exact Or.inl (lt_of_lt_of_le (heR' ▸ h1) hle)
      · exact Or.inr (hlone l ls eL (fun y hy => hL.1 y hy) heL (le_antisymm
          (by rw [h1, heR']; exact hle) hl1))
    -- an auxiliary fact
    · have := FiniteSignal.valueAt_singleton r t
      rw [this] at hy; exact (Option.some.inj hy).symm

/-- The properties of the loop: the first value, validity of the result, its last time and its
value at every time up to the end of the shorter signal. -/
theorem aux_combineLoop_props {T V W : Type} [LinearOrder T] [DecidableEq W] (op : V → V → W)
    (n : ℕ) : -- --- CONCL ---
    ∀ (l r : T × V) (ls rs : List (T × V)), ls.length + rs.length + 2 = n →
      ((l :: ls).map Prod.fst).Pairwise (· < ·) → ((r :: rs).map Prod.fst).Pairwise (· < ·) →
      ∀ eL eR : T, aux_IsLast eL ((l :: ls).map Prod.fst) →
      aux_IsLast eR ((r :: rs).map Prod.fst) →
      ((FiniteSignal.combineLoop op (l :: ls) (r :: rs)).map Prod.snd).head? =
          some (op l.2 r.2) ∧
        ((FiniteSignal.combineLoop op (l :: ls) (r :: rs)).map Prod.fst).Pairwise (· < ·) ∧
        ((FiniteSignal.combineLoop op (l :: ls) (r :: rs)).map Prod.snd).IsChain (· ≠ ·) ∧
        (∀ x ∈ (FiniteSignal.combineLoop op (l :: ls) (r :: rs)).map Prod.fst, min l.1 r.1 ≤ x) ∧
        aux_IsLast (min eL eR) ((FiniteSignal.combineLoop op (l :: ls) (r :: rs)).map Prod.fst) ∧
        ∀ t x y, FiniteSignal.valueAt (l :: ls) t = some x →
          FiniteSignal.valueAt (r :: rs) t = some y → (t < eL ∧ t < eR ∨ eL = eR ∧ t = eL) →
          FiniteSignal.valueAt (FiniteSignal.combineLoop op (l :: ls) (r :: rs)) t =
            some (op x y) := by -- --- PROOF ---
  -- case analysis
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l r ls rs hn hL hR eL eR heL heR
  have hL' := hL
  have hR' := hR
  rw [List.map_cons, List.pairwise_cons] at hL' hR'
  have hls : ∀ y ∈ ls, l.1 < y.1 := fun y hy => hL'.1 y.1 (List.mem_map_of_mem hy)
  have hrs : ∀ y ∈ rs, r.1 < y.1 := fun y hy => hR'.1 y.1 (List.mem_map_of_mem hy)
  obtain ⟨t₀, ls', rs', hE, hB1, hB2, hmin, hA1, hA2⟩ :=
    FiniteSignal.combineLoop_step op l r ls rs hls hrs
  rw [hE]
  have ht1 : t₀ ≤ l.1 := hmin ▸ min_le_left _ _
  have ht2 : t₀ ≤ r.1 := hmin ▸ min_le_right _ _
  by_cases hnil : ls' = [] ∨ rs' = []
  · -- one signal is used up: a single breakpoint
    -- the fact `hO`
    have hO : FiniteSignal.combineEmit op t₀ (op l.2 r.2) ls' rs'
        (FiniteSignal.combineLoop op ls' rs') = [(t₀, op l.2 r.2)] := by
      unfold FiniteSignal.combineEmit
      rcases hnil with rfl | rfl
      · rfl
      · cases ls' <;> rfl
    rw [hO]
    obtain ⟨h6, h7⟩ := aux_combineLoop_single l r ls rs hL hR eL eR t₀ heL heR hmin ls' rs' hA1 hA2
      hnil
    refine ⟨rfl, by simp, by simp, by simp [hmin], ?_, fun t x y hx hy hok => ?_⟩
    · exact ⟨by simp [h6], by simp [h6]⟩
    · obtain ⟨rfl, rfl⟩ := h7 t x y hx hy hok
      simp [FiniteSignal.valueAt_singleton]
  · -- both have a next breakpoint
    -- rewrite and simplify
    rw [not_or] at hnil
    obtain ⟨hn1, hn2⟩ := hnil
    obtain ⟨l', ls'', rfl⟩ := List.exists_cons_of_ne_nil hn1
    obtain ⟨r', rs'', rfl⟩ := List.exists_cons_of_ne_nil hn2
    -- the data of the remaining breakpoints
    have hsL : ((l' :: ls'').map Prod.fst).Pairwise (· < ·) := by
      rcases hA1 with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]; exact hL'.2
      · rw [h1]; exact hL
    have hsR : ((r' :: rs'').map Prod.fst).Pairwise (· < ·) := by
      rcases hA2 with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]; exact hR'.2
      · rw [h1]; exact hR
    have heL2 : aux_IsLast eL ((l' :: ls'').map Prod.fst) := by
      rcases hA1 with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1] at hn1 ⊢
        exact aux_isLast_tail eL l.1 _ (fun y hy => by
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy; exact hls z hz) heL (by simpa using hn1)
      · rw [h1]; exact heL
    -- the fact `heR2`
    have heR2 : aux_IsLast eR ((r' :: rs'').map Prod.fst) := by
      rcases hA2 with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1] at hn2 ⊢
        exact aux_isLast_tail eR r.1 _ (fun y hy => by
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy; exact hrs z hz) heR (by simpa using hn2)
      · rw [h1]; exact heR
    have hlen : ls''.length + rs''.length + 2 < n := by
      rcases hA1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases hA2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
      all_goals first
        | (have l1 := congrArg List.length h1; have l2 := congrArg List.length h2
           simp only [List.length_cons] at l1 l2; omega)
        | (exfalso; rcases le_total l.1 r.1 with h | h
           · exact absurd (hmin.trans (min_eq_left h)) (ne_of_lt h1')
           · exact absurd (hmin.trans (min_eq_right h)) (ne_of_lt h2'))
    -- unpack the facts from the previous steps
    obtain ⟨q4, q2, q3, q5, q6, q7⟩ := ih _ hlen l' r' ls'' rs'' rfl hsL hsR eL eR heL2 heR2
    -- the breakpoints the loop yields for the remaining ones
    obtain ⟨w, rest, hw⟩ : ∃ w rest, FiniteSignal.combineLoop op (l' :: ls'') (r' :: rs'') =
        w :: rest := by
      cases hO : FiniteSignal.combineLoop op (l' :: ls'') (r' :: rs'') with
      | nil => simp [hO] at q4
      | cons w rest => exact ⟨w, rest, rfl⟩
    rw [hw] at q2 q3 q4 q5 q6 q7 ⊢
    have hw2 : w.2 = op l'.2 r'.2 := by simpa using q4
    have hlt : t₀ < min l'.1 r'.1 := lt_min (hB1 l' (by simp)) (hB2 r' (by simp))
    have hgt : ∀ x ∈ (w :: rest).map Prod.fst, t₀ < x := fun x hx => lt_of_lt_of_le hlt (q5 x hx)
    -- below `t₀` both signals hold their first value
    have hbelow : ∀ t x y, t < t₀ → FiniteSignal.valueAt (l :: ls) t = some x →
        FiniteSignal.valueAt (r :: rs) t = some y → x = l.2 ∧ y = r.2 := fun t x y ht hx hy =>
      ⟨aux_valueAt_first l ls t x (Or.inl (ht.trans_le ht1)) hx,
        aux_valueAt_first r rs t y (Or.inl (ht.trans_le ht2)) hy⟩
    -- from `t₀` on, the remaining breakpoints decide
    have hon : ∀ t x y, ¬ t < t₀ → FiniteSignal.valueAt (l :: ls) t = some x →
        FiniteSignal.valueAt (r :: rs) t = some y → (t < eL ∧ t < eR ∨ eL = eR ∧ t = eL) →
        FiniteSignal.valueAt (w :: rest) t = some (op x y) := by
      intro t x y ht hx hy hok
      refine q7 t x y ?_ ?_ hok
      · rcases hA1 with ⟨h1, h2⟩ | ⟨h1, -⟩
        · rw [h1]
          rwa [FiniteSignal.valueAt_cons_of_ge l ls t (by rw [← h2]; exact ht)
            (h1 ▸ List.cons_ne_nil _ _)] at hx
        · rw [h1]; exact hx
      · rcases hA2 with ⟨h1, h2⟩ | ⟨h1, -⟩
        · rw [h1]
          rwa [FiniteSignal.valueAt_cons_of_ge r rs t (by rw [← h2]; exact ht)
            (h1 ▸ List.cons_ne_nil _ _)] at hy
        -- rewrite and simplify
        · rw [h1]; exact hy
    have hem : FiniteSignal.combineEmit op t₀ (op l.2 r.2) (l' :: ls'') (r' :: rs'') (w :: rest) =
        if op l.2 r.2 ≠ op l'.2 r'.2 then (t₀, op l.2 r.2) :: w :: rest else w :: rest := rfl
    rw [hem]
    by_cases hv : op l.2 r.2 ≠ op l'.2 r'.2
    · rw [if_pos hv]
      refine ⟨by simp, ?_, ?_, ?_, ?_, fun t x y hx hy hok => ?_⟩
      · rw [List.map_cons, List.pairwise_cons]; exact ⟨hgt, q2⟩
      · simp only [List.map_cons]
        exact List.isChain_cons_cons.mpr ⟨by rw [← hw2] at hv; simpa using hv, q3⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hmin ▸ le_rfl
        · exact hmin ▸ (hgt x hx).le
      -- prove the parts of the goal
      · refine ⟨List.mem_cons_of_mem _ q6.1, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (hgt _ q6.1).le
        · exact q6.2 x hx
      · by_cases ht : t < t₀
        · rw [FiniteSignal.valueAt_cons_of_lt _ _ t ht]
          obtain ⟨rfl, rfl⟩ := hbelow t x y ht hx hy
          rfl
        · rw [FiniteSignal.valueAt_cons_of_ge _ _ t ht (List.cons_ne_nil _ _)]
          exact hon t x y ht hx hy hok
    · rw [if_neg hv]
      have hv' : op l.2 r.2 = op l'.2 r'.2 := not_not.mp hv
      refine ⟨by simp [hv', hw2], q2, q3, ?_, q6, fun t x y hx hy hok => ?_⟩
      · intro x hx; rw [← hmin]; exact (hgt x hx).le
      -- split on whether the condition holds
      · by_cases ht : t < t₀
        · have hwt : t < w.1 := ht.trans (hgt w.1 (by simp))
          rw [FiniteSignal.valueAt_cons_of_lt _ _ t hwt]
          obtain ⟨rfl, rfl⟩ := hbelow t x y ht hx hy
          rw [hw2, hv']
        · exact hon t x y ht hx hy hok

theorem aux_zip_map_fst_snd {α β : Type} (O : List (α × β)) :
    (O.map Prod.fst).zip (O.map Prod.snd) = O := by
  induction O with
  | nil => rfl
  | cons p q ih => simp [ih]

/-- The pairs of a valid signal are a non-empty list with sorted times ending at the duration. -/
theorem aux_valid_pairs {T V : Type} [LinearOrder T] [Zero T] (s : FiniteSignal T V)
    (hs : s.IsValid) : -- --- CONCL ---
    ∃ p ps, s.pairs = p :: ps ∧ ((p :: ps).map Prod.fst).Pairwise (· < ·) ∧
      aux_IsLast s.duration ((p :: ps).map Prod.fst) ∧ 0 ≤ p.1 := by -- --- PROOF ---
  obtain ⟨hmem, hle⟩ := FiniteSignal.time_le_duration s hs
  obtain ⟨hne, hl, hp, -, hnn⟩ := hs
  have hmap : s.pairs.map Prod.fst = s.time := by
    simp [FiniteSignal.pairs, List.map_fst_zip, hl]
  cases hq : s.pairs with
  | nil => exact absurd (by rw [← hmap, hq]; rfl) hne
  | cons p ps =>
    rw [hq] at hmap
    exact ⟨p, ps, rfl, hmap ▸ hp, ⟨hmap ▸ hmem, fun x hx => hle x (hmap ▸ hx)⟩,
      hnn _ (hmap ▸ List.mem_map_of_mem (List.mem_cons_self))⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.combine?_spec {T V W : Type} [LinearOrder T] [Zero T] [DecidableEq W]
    (op : V → V → W) (lhs rhs : FiniteSignal T V) (hl : lhs.IsValid)
    (hr : rhs.IsValid) : -- --- CONCL ---
    ∃ r, FiniteSignal.combine? op [lhs, rhs] = some r ∧ r.IsValid ∧
      r.duration = min lhs.duration rhs.duration ∧ ∀ t x y, lhs.at? t = some x →
        rhs.at? t = some y → (t < lhs.duration ∧ t < rhs.duration ∨
          lhs.duration = rhs.duration ∧ t = lhs.duration) →
        r.at? t = some (op x y) := by -- --- PROOF ---
  -- the pairs of both signals, and the properties of the loop on them
  obtain ⟨l, ls, hL, hsL, heL, hl0⟩ := aux_valid_pairs lhs hl
  obtain ⟨r, rs, hR, hsR, heR, hr0⟩ := aux_valid_pairs rhs hr
  obtain ⟨q4, q2, q3, q5, q6, q7⟩ := aux_combineLoop_props op _ l r ls rs rfl hsL hsR _ _ heL heR
  set O := FiniteSignal.combineLoop op (l :: ls) (r :: rs) with hO
  -- the checks of the constructor pass
  have hne : O.map Prod.fst ≠ [] := by
    intro h
    have : O.map Prod.snd = [] := by
      rw [List.map_eq_nil_iff] at h ⊢; exact h
    simp [this] at q4
  have hv : (⟨O.map Prod.fst,
      O.map Prod.snd⟩ : FiniteSignal T W).IsValid :=
    ⟨hne, by simp, q2, q3, fun t ht => (le_min hl0 hr0).trans (q5 t ht)⟩
  have hmk : FiniteSignal.combine? op [lhs, rhs] = some ⟨O.map Prod.fst, O.map Prod.snd⟩ := by
    show FiniteSignal.mk? ((FiniteSignal.combineLoop op lhs.pairs rhs.pairs).map Prod.fst)
      ((FiniteSignal.combineLoop op lhs.pairs rhs.pairs).map Prod.snd) = _
    rw [hL, hR]
    exact (FiniteSignal.mk?_eq_some_iff _ _ _).mpr ⟨rfl, rfl, hv⟩
  refine ⟨_, hmk, hv, ?_, fun t x y hx hy hok => ?_⟩
  · -- the duration is the shorter one
    -- unpack the facts from the previous steps
    obtain ⟨hm, hle⟩ := FiniteSignal.time_le_duration _ hv
    exact le_antisymm (q6.2 _ hm) (hle _ q6.1)
  · -- the value, read off the loop
    rw [FiniteSignal.at?_eq_valueAt lhs hl.2.1 t] at hx
    rw [FiniteSignal.at?_eq_valueAt rhs hr.2.1 t] at hy
    by_cases h1 : 0 ≤ t ∧ t ≤ lhs.duration
    · rw [if_pos h1, hL] at hx
      by_cases h2 : 0 ≤ t ∧ t ≤ rhs.duration
      · rw [if_pos h2, hR] at hy
        obtain ⟨hm, hle⟩ := FiniteSignal.time_le_duration _ hv
        have hdur : (⟨_, _⟩ : FiniteSignal T W).duration = min lhs.duration rhs.duration :=
          le_antisymm (q6.2 _ hm) (hle _ q6.1)
        have hle' : t ≤ (⟨O.map Prod.fst, O.map Prod.snd⟩ : FiniteSignal T W).duration := by
          rw [hdur]; exact le_min h1.2 h2.2
        -- rewrite and simplify
        rw [FiniteSignal.at?_eq_valueAt _ (by simp) t, if_pos ⟨h1.1, hle'⟩]
        simp only [FiniteSignal.pairs, aux_zip_map_fst_snd]
        exact q7 t x y hx hy hok
      · rw [if_neg h2] at hy; exact absurd hy (by simp)
    · rw [if_neg h1] at hx; exact absurd hx (by simp)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
