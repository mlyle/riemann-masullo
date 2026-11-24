# The class field theory input of Remark 7.1.3.1

This directory is a Lake library of its own, `RiemannMasulloClassField`, and one of the default
targets of the package: `lake build` builds it with everything else.

It proves the one statement of the project that needs global class field theory. For a unitary
character of finite order of the idele class group of a number field `F`, there is a number
field `L` over `F` such that the character is unramified, with local value one, at every prime
of `F` under a prime of `L` of ramification index and residue degree one
(`RiemannMasullo.FiniteOrderCharacterSplitsInClassField`, stated in
`RiemannMasullo/Ch07_SchauderBasesZeta/Sec1b.lean`). Remark 7.1.3.1, p. 324, of the paper says
"By Chebotarev" at this point. The main library proves the remark from that statement as a
named hypothesis; [`Remark7131.lean`](Remark7131.lean) proves the statement, and with it the
remark outright.

## Where the proof comes from

The existence theorem of global class field theory is taken from Naganori Yamaguchi's
formalization, [n-yamaguchi-0729/ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory)
(Apache-2.0, Copyright (c) 2026 Naganori Yamaguchi), pinned in `lakefile.toml` and
`lake-manifest.json` at commit `fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565`, as the Lake package
`Nyll`. That library is on the same Lean and the same Mathlib commit as this project, so it is
used as it stands, as a dependency. Nothing of it is copied into this repository.

The proof applies `GlobalClassFieldTheory.GlobalClassFields.exists_closedFiniteIndexClassField_original`
to the kernel of the character, which is closed of finite index. At a prime with ramification
index and residue degree one the decomposition group is trivial, so the prime splits
completely, every one-place idele class there is a norm, and the character is trivial on it.

## Why it is a library of its own

The proof needs about 1,200 files and 420,000 lines of the dependency, almost as much as all
of `RiemannMasullo/`. Compiling them takes about five hours of one processor core (a few
minutes on a large machine, about an hour on a continuous-integration runner), once; after
that Lake reuses the result.

Nothing in `RiemannMasullo/` imports this library, so `lake build RiemannMasullo` does not
compile the dependency. The checks that run on every pull request build the main library and
the comparator files in that way. The workflow `Full build` builds everything, this library
included, every week, on demand, and for any pull request that touches this directory or the
files that pin the dependencies.

The statements proved here show only `propext`, `Classical.choice` and `Quot.sound` under
`#print axioms`.
