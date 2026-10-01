import CORALean.Examples.Bench.Cli
import CORALean.Examples.Bench.GitInfo
import CORALean.Examples.Bench.RandVerifyDirSearch
import CORALean.Examples.Bench.RandVerifyDyadicOut
import CORALean.Examples.Bench.RandVerifyNumber
import CORALean.Examples.Bench.RandVerifyParse
import CORALean.Examples.Bench.RandVerifyReference
import CORALean.Examples.Bench.RandVerifySci
import CORALean.Examples.Bench.RandVerifySupportGap

/-!
# `lake exe bench randverify-family --in FILE [--dt Q] [--eta K] [--order R] [--check C] ...`

EXPLORATORY: `randverify` instances of `relError = 10^-i`, `i = 1, …, 12`, from the instance `--in`
(its system, `X0`, `U`, `tend` and box shapes kept), to `<out>/randverify-family/`.

1. The reference: the exact output windows (`referenceWindows`) of the wrapping-free reach at
   `Dyadic P` (`--prec`, `1024`), `--dt` (`1/256`), `--eta` (`10`), `--order` (`400`). Sound.
2. Per unsafe box `S`, the rational unit `ℓ` (`ratUnit t`, `bestDirection`) along which `S` is
   farthest beyond every window, and that support gap `h_ref` (`supportGap`), exactly.
3. Per `r`, `ε = r · Σ_i width_i(X0)`, and `S` translated by `(ε - h_ref) ℓ`, so its gap is exactly
   `ε`; stored rounded outward at `2^-80`, and its gap `h_stored ∈ [ε - 2^-79, ε]` recomputed.

So every instance is satisfiable with true support gap `≥ h_stored`. The change of the gap on a
second reference (`--check DT,ETA,ORDER`, default `dt / 2`) indicates the reference's own
overestimation `refErr`: the true gap is in `[ε, ε + refErr]`. CORA's generator instead places a
box to touch CORA's own `ε`-accurate outer set, a true gap in `[0, ε]`: this family is not CORA's.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An exact rational and its value, `{"exact": "num/den", "decimal": "..."}`. -/
def aux_famRat (q : ℚ) : Json :=
  Json.mkObj [("exact", Json.str s!"{q.num}/{q.den}"),
    ("decimal", Json.str (sciString (quotFloat q.num q.den)))]

/-- `"1e-07"`, the name `10^-i` goes by. -/
def aux_relName (i : ℕ) : String := if i < 10 then s!"1e-0{i}" else s!"1e-{i}"

/-- The box `S` translated by `δ ℓ`, `ℓ = p / q`, rounded outward at `2^-e`. -/
def aux_placed (S : Array (ℚ × ℚ)) (p : ℤ × ℤ) (q : ℕ) (δ : ℚ) (e : ℕ) :
    Array ((String × ℚ) × (String × ℚ)) :=
  (S.zip #[(p.1 : ℚ) / q, (p.2 : ℚ) / q]).map fun ((l, h), ℓi) =>
    (roundDyadicOut (l + δ * ℓi) e false, roundDyadicOut (h + δ * ℓi) e true)

/-- The windows at `dt`, timed, or the reason there are none. -/
def aux_famReference (I : RandInstance) (p : ℕ) (dt : ℚ) (η ρ : ℕ) :
    IO (List RandOutZono × Float) := do
  let t0 ← IO.monoNanosNow
  let Ys ← IO.ofExcept (referenceWindows I p dt η ρ |>.mapError fun e =>
    s!"randverify-family: reference at dt = {dt}: {e}")
  let cs : ℕ := Ys.foldl (fun a Y => a + Y.den + Y.gens.size) 0
  if cs = 4242424242424242 then IO.eprintln "randverify-family: checksum" else pure ()
  let t1 ← IO.monoNanosNow
  pure (Ys, ((t1 - t0 : ℕ).toFloat) / 1e9)


-- =====================================  MAIN DEFINITION  ====================================== --

def runRandVerifyFamily (args : CliArgs) : IO Unit := do
  -- the source instance and the reference's settings
  let src ← match args.inFile with
    | some f => pure (System.FilePath.mk f)
    | none => throw (IO.userError "randverify-family: `--in FILE` names the source instance")
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile src) |>.mapError fun e => s!"{src}: {e}")
  let srcName := src.fileStem.getD src.toString
  let I ← IO.ofExcept (parseRandInstance srcName j |>.mapError fun e => s!"{src}: {e}")
  let dtS := args.dt.getD "1/256"
  let dt ← IO.ofExcept (parseRandString dtS)
  let η := args.eta.getD 10
  let ρ := args.order.getD 400
  let p := args.prec.getD 1024
  let e := 80
  -- the second reference's settings, `dt / 2` unless `--check` says otherwise
  let (dt2S, η₂, ρ₂) ← match args.check.map fun c => (c.splitOn ",").map (·.trimAscii.toString) with
    | none => pure (s!"{(dt / 2).num}/{(dt / 2).den}", η, ρ)
    | some [d, k, r] => match k.toNat?, r.toNat? with
      | some k, some r => pure (d, k, r)
      | _, _ => throw (IO.userError "randverify-family: `--check` is `DT,ETA,ORDER`")
    | some _ => throw (IO.userError "randverify-family: `--check` is `DT,ETA,ORDER`")
  let dt₂ ← IO.ofExcept (parseRandString dt2S)
  -- the two, on two threads
  let job1 ← IO.asTask (prio := .dedicated) (aux_famReference I p dt η ρ)
  let job2 ← IO.asTask (prio := .dedicated) (aux_famReference I p dt₂ η₂ ρ₂)
  let (Ys, tRef) ← IO.ofExcept job1.get
  IO.println s!"randverify-family: reference, {Ys.length} windows, {tRef} s"
  let (Ys2, tRef2) ← IO.ofExcept job2.get
  IO.println s!"randverify-family: check reference, {Ys2.length} windows, {tRef2} s"
  -- per unsafe box: the direction, the gap there, and the gap on the check
  let specs ← I.unsafeSets.mapM fun S => do
    let t := bestDirection Ys S 360 50
    let some h := supportGap Ys S t | throw (IO.userError "randverify-family: no window")
    let some h2 := supportGap Ys2 S t | throw (IO.userError "randverify-family: no window")
    IO.println s!"randverify-family: t = {t}, h_ref = {sciString (quotFloat h.num h.den)}, change \
      at the check = {sciString (quotFloat (h2 - h).num (h2 - h).den)}"
    pure (S, t, h, h2)
  let widthSum := I.x0.foldl (fun s (l, h) => s + (h - l)) (0 : ℚ)
  let dir := System.FilePath.mk args.outDir / "randverify-family"
  IO.FS.createDirAll dir
  let commit ← gitCommit
  for i in (List.range 12).map (· + 1) do
    let r : ℚ := 1 / 10 ^ i
    let ε := r * widthSum
    -- each box placed at gap `ε` along its direction, stored outward, its gap recomputed
    let placed ← specs.mapM fun (S, t, h, h2) => do
      let ((p₁, p₂), q) := ratUnit t
      let B := aux_placed S (p₁, p₂) q (ε - h) e
      let some hs := supportGap Ys (B.map fun ((_, l), (_, u)) => (l, u)) t
        | throw (IO.userError "randverify-family: no window")
      if hs < ε - 2 / 2 ^ e ∨ ε < hs then
        throw (IO.userError s!"randverify-family: stored gap {hs} outside [ε - 2^-79, ε]")
      let specJ := Json.mkObj
        [ ("t", Json.str s!"{t.num}/{t.den}"),
          ("ell", Json.arr #[Json.str s!"{p₁}/{q}", Json.str s!"{p₂}/{q}"]),
          ("h_ref_source", aux_famRat h), ("delta", aux_famRat (ε - h)),
          ("h_stored", aux_famRat hs), ("h_ref_source_check", aux_famRat h2),
          ("ref_change_check", aux_famRat (h2 - h)) ]
      pure (B, specJ)
    -- the file: the source's fields, the new boxes, the family's metadata
    let boxes := Json.arr (placed.map fun (B, _) => Json.mkObj
      [ ("type", Json.str "interval"),
        ("lowerbound", Json.arr (B.map fun ((l, _), _) => Json.str l)),
        ("upperbound", Json.arr (B.map fun (_, (u, _)) => Json.str u)) ])
    let family := Json.mkObj
      [ ("relError", Json.str (aux_relName i)), ("relErrorExact", Json.str s!"1/{10 ^ i}"),
        ("sumWidthX0", aux_famRat widthSum), ("epsilon", aux_famRat ε),
        ("epsilonFormula", Json.str "relError * sum_i width_i(X0)"),
        ("roundingGrid", Json.str s!"2^-{e}"),
        ("specs", Json.arr (placed.map (·.2))),
        ("reference", Json.mkObj
          [ ("type", Json.str s!"dyadic{p}"), ("algorithm", Json.str "wrappingfree"),
            ("dt", Json.str dtS), ("eta", Lean.toJson η), ("order", Lean.toJson ρ),
            ("windows", Lean.toJson Ys.length), ("time_s", Lean.toJson tRef),
            ("check_dt", Json.str dt2S), ("check_eta", Lean.toJson η₂),
            ("check_order", Lean.toJson ρ₂),
            ("check_windows", Lean.toJson Ys2.length), ("check_time_s", Lean.toJson tRef2) ]),
        -- what the family promises, and how it differs from CORA's
        ("source", Json.str srcName), ("gitCommit", Json.str commit),
        ("guarantee", Json.str "the true reachable set lies inside the reference, so each \
          instance is satisfiable with true support gap >= h_stored >= epsilon - 2^-79 along \
          ell; the true gap is in [epsilon, epsilon + refErr], refErr the reference's \
          overestimation, of which ref_change_check is an indication"),
        ("placement", Json.str "not CORA's: CORA's box touches CORA's own epsilon-accurate \
          outer set, so its true gap is in [0, epsilon]; here it is in \
          [epsilon, epsilon + refErr]") ]
    let fields := match j with
      | .obj kvs => kvs.toList.filter fun (k, _) =>
        k ∉ ["unsafeSet", "cora", "generator", "relError", "satisfiable", "family"]
      | _ => []
    let out := Json.mkObj (fields ++
      [ ("generator", Json.str s!"CORALean randverify-family from {srcName}"),
        ("relError", Json.str (aux_relName i)), ("satisfiable", Json.bool true),
        ("unsafeSet", boxes), ("family", family) ])
    let path := dir / s!"rand_family_{aux_relName i}.json"
    IO.FS.writeFile path out.compress
    IO.println s!"randverify-family: wrote {path}"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
