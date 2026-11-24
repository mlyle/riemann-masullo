# Critical-line zero count for Chapter 10

This branch supplies a Lean 4.36 reproduction for [#6742](https://github.com/mccorvie/riemann-masullo/issues/6742) and the original [#5231](https://github.com/mccorvie/riemann-masullo/issues/5231). For each natural number `k`, it constructs a height `T` and a finite set of more than `(k + 1) * (T + 1)` distinct ordinates in `(0,T]` where the Riemann zeta function vanishes on the critical line. The argument combines the dyadic Riemann–von Mangoldt estimate with Zeta23 Theorem A on distinct zeros.

The target patch replaces the existing private arithmetic admission and checks the entire `RiemannMasullo.Ch10_TraceSpectral.Sec3_Printed` module under its original name. The printed uniform biorthogonal bound in equation (10.3.1.18), p. 451, then has a Lean refutation using only `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduction

Use Python 3.11 or newer, Git, Elan and Lake. Run these commands from the project at this research commit. The script writes generated sources and compiled artifacts to a temporary directory and prints its path. Pass `--work /path/to/an/empty/directory` to retain them at a chosen location. The initial Lake command obtains the Mathlib cache.

```sh
git clone --branch research/critical-zero-count-lean436 https://github.com/mlyle/riemann-masullo.git
git clone https://github.com/teal-sea/zeta-lab.git
git -C zeta-lab checkout a401821c9608526425f3d4cf7ff8e59bc37e1c79
cd riemann-masullo
lake exe cache get
python3 research/critical-zero-count/replay.py --repo . --upstream ../zeta-lab
```

The project source is pinned to [8b40f11](https://github.com/mccorvie/riemann-masullo/commit/8b40f11bf88cc95e2cb84fcea6d6f4dd81e4b932). The external source is the existing project vendor's [zeta-lab pin](https://github.com/teal-sea/zeta-lab/tree/a401821c9608526425f3d4cf7ff8e59bc37e1c79/lean/vendor/zeta23), which ports [Anthropic's Zeta23](https://github.com/anthropics/zeta-23-lean/tree/3635e74826a4c1fcece7d1cd2b6fa75e43a00510). Source notices and licenses accompany the corresponding pinned sources. [Project provenance](https://github.com/mccorvie/riemann-masullo/blob/8b40f11bf88cc95e2cb84fcea6d6f4dd81e4b932/RiemannMasullo/External/ZetaLab/Zeta23.UPSTREAM.md)

## Files

- `replay.py` follows imports starting at `Zeta23.Final`. It maps imports of complete vendored modules to `RiemannMasullo.External.ZetaLab`, builds the remaining 95 modules under their original Zeta23 names, then compiles the arithmetic proof, the original target module, and its audit.
- `native-compat.patch` records the proof and import changes needed in 11 source files for Lean 4.36. It applies after import-path relocation.
- `UnconditionalCount.lean` applies `Zeta23.riemannVonMangoldt_zeta` and `Zeta23.thmA₀` to the Chapter 10 arithmetic reduction.
- `chapter10-target.patch` contains the additional import and the proof of `spectralLineJet_rational_critical_zero_count`.
- `CriticalAudit.lean` checks the transitive axiom set of both external theorems, the arithmetic adapter, the original private count, and the public refutation. It also traverses used constants to check for `sorryAx`.

A project PR for the small Chapter 10 patch needs the supplemental proof modules to be available to the project build. This research branch gives the integrator the source changes and the replay independently of that dependency decision.

[Recorded Lean checks](verification.txt) include the full proof-term audit with private module data available and the before-and-after public signature comparison.
