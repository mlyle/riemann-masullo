# Dixmier–Malliavin factorization

[Anthropic’s Fermat formalization](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2)
supplies the analytic input for real-line factorization in §10.3. Copyright 2026 Anthropic, PBC.
The original [license](LICENSE) and [notice](../licenses/anthropics-fermats-last-theorem.NOTICE) accompany the port.

[OneVariable.lean](OneVariable.lean) constructs the compactly supported kernels that recover evaluation at zero.
[OneParameter.lean](OneParameter.lean) applies this identity along the flow of an exponential in a real normed algebra.
[SOURCE_MAP.json](SOURCE_MAP.json) records the upstream paths and hashes, and [MODIFICATIONS.md](MODIFICATIONS.md) describes the port.
