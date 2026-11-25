# Signed prime curvature on the fourth-power grid

The explicit unconditional upper bound for the sum of the negative parts of the centered rational first-prime Riesz samples is J⁷ for every J through **1,750,000,000,000**. For the real primitive character modulo four the corresponding bound holds through **16,000,000**. [Definitions, proof and two interval receipts](spectral-interpolation-rational-deficit-smoothed.md).

Each Python script accepts `--precision 128` or `--precision 192` and needs python-flint 0.9.0. From this directory, the following command replays the final one-sided estimate.

```sh
python spectral-interpolation-rational-deficit-smoothed.py --precision 192
```

The [finite density certificate](spectral-interpolation-rational-deficit-density.md), the [sample mean-square estimates](spectral-interpolation-mod4-deficit-large-sieve.md) and the [initial modulo-four calculations](spectral-interpolation-mod4-deficit.md) give the preceding bounds and their primary sources. They include initial prime samples, proper prime powers, archimedean residues, verified heights and zero counts. The calculations establish a finite interval. The estimate at arbitrarily large cutoffs is open.
