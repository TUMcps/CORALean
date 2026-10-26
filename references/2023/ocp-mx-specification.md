# OCP Microscaling Formats (MX) Specification, Version 1.0

```bibtex
@manual{ocp2023mx,
  author = {{Open Compute Project}},
  title = {OCP Microscaling Formats (MX) Specification, Version 1.0},
  publisher = {Open Compute Project},
  year = {2023}
}
```

**Source:** https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf (16 pages, September 2023, text extracted with `pymupdf`, Sections 5.2-5.3 read)  
**Inventory:** partial (only the element data types a CORALean float format takes, Tables 2 and 5; the scale types, the operations of Section 6 and the other element types are not rows)

The specification lists the concrete MX element formats and their encodings. CORALean takes two
of them, FP8 E4M3 and FP4 E2M1, as formats of the IEEE-style scalar `IEEE fmt`. Table 2 of the
specification reproduces the FP8 encoding table of the OCP 8-bit Floating Point Specification
(OFP8), which was not read separately.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Table 2` | (FP8 encoding details) E4M3 has exponent bias 7, no infinities, one NaN encoding `S 1111 111`, largest normal ± 2⁸ × 1.75 = ± 448, smallest normal ± 2⁻⁶ and smallest subnormal ± 2⁻⁹. | [`IEEE.lean`](../../src/CORALean/Global/Float/Instances/IEEE/IEEE.lean) — `IEEEFormat.e4m3`, the finite grid of the format | `correct` |
| `Table 5` | (FP4 encoding details) E2M1 has exponent bias 1, no infinities or NaN, largest normal ± 2² × 1.5 = ± 6, smallest normal ± 1 and smallest subnormal ± 0.5. | [`IEEE.lean`](../../src/CORALean/Global/Float/Instances/IEEE/IEEE.lean) — `IEEEFormat.e2m1`, the finite grid of the format | `correct` |
