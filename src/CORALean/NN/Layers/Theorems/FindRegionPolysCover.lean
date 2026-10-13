import CORALean.NN.Layers.Operations.FindRegionPolys
import CORALean.NN.Layers.Theorems.FindRegionLoopCover

/-!
# `findRegionPolys`: every point has a polynomial within the error
If the fit `F` is a sound relaxation of `σ` at every order and the two infinite ends are
polynomials that enclose `σ` on `(-∞, l_max]` and `[u_max, ∞)` as given, then the regions
`findRegionPolys` returns cover the whole line, each polynomial encloses `σ` within its error on
its region, and every region found, as opposed to the two given, has error at most `tol`.
Outer: an enclosure of `σ` by polynomial and error, not `σ` itself.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Each `t` lies in a returned region whose polynomial is within its error of `σ t`. -/
theorem findRegionPolys_cover {σ : ℝ → ℝ} {F : (o : ℕ) → PolyRelaxation 𝕋 o}
    (hF : ∀ o, (F o).Sound σ) (order : ℕ) (tol : 𝕋) (fuel : ℕ) (lMax uMax : 𝕋)
    {pStart pEnd : RegionPoly 𝕋} (hs : pStart.lo = none ∧ pStart.hi = some lMax)
    (he : pEnd.lo = some uMax ∧ pEnd.hi = none) (hS : pStart.Encloses σ) (hE : pEnd.Encloses σ)
    {regions : List (RegionPoly 𝕋)}
    (h : findRegionPolys F order tol fuel lMax uMax pStart pEnd = some regions) :
    (∀ t, ∃ r ∈ regions, r.covers t ∧
        |σ t - Real.evalPoly (fun k => toReal (r.coeffs k)) t| ≤ toReal r.err) ∧
      ∀ r ∈ regions, r = pStart ∨ r = pEnd ∨ toReal r.err ≤ toReal tol := by -- --- PROOF ---
  -- the loop's regions, framed by the two given ones
  unfold findRegionPolys at h
  obtain ⟨mids, hm, rfl⟩ := Option.map_eq_some_iff.mp h
  have hcov : ∀ t, (t ≤ toReal lMax ∨ toReal uMax ≤ t) →
      ∃ r ∈ [pStart, pEnd] ++ ([] : List (RegionPoly 𝕋)), r.covers t := by
    intro t ht
    rcases ht with hl | hu
    · exact ⟨pStart, by simp, fun a ha => by simp [hs.1] at ha, fun b hb => by
        rw [hs.2] at hb; exact (Option.some.inj hb) ▸ hl⟩
    · exact ⟨pEnd, by simp, fun a ha => by
        rw [he.1] at ha; exact (Option.some.inj ha) ▸ hu, fun b hb => by simp [he.2] at hb⟩
  obtain ⟨h1, -, h3⟩ := findRegionLoop_cover hF order tol [pStart, pEnd] fuel lMax uMax [] mids
    (by simp) hcov hm
  -- every region encloses `σ`: the loop's by its theorem, the two given by hypothesis
  have hall : ∀ r ∈ pStart :: (mids ++ [pEnd]), r.Encloses σ := by
    intro r hr
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr | rfl
    · exact hS
    · exact (h1 r hr).1
    · exact hE
  -- coverage from the loop (which ends with nothing outside it), then the error bound
  refine ⟨fun t => ?_, fun r hr => ?_⟩
  · obtain ⟨r, hr, hc⟩ := h3 t
    have hr' : r ∈ pStart :: (mids ++ [pEnd]) := by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      tauto
    exact ⟨r, hr', hc, hall r hr' t hc⟩
  · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr | hr
    · exact Or.inl hr
    · exact Or.inr (Or.inr (h1 r hr).2)
    · exact Or.inr (Or.inl hr)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
