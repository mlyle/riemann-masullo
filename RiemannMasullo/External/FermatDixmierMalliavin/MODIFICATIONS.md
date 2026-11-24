# Modifications

- Converted both solutions to Lean modules. Exported their conclusions under the upstream
  theorem names in the `DixmierMalliavin` namespace, with docstrings and private helpers.
- Removed the statement wrappers and their P2M elaborator dependency. The one-parameter proof
  imports the ported one-variable theorem directly.
- In the one-variable proof, placed `shift` and `shiftN` in their enclosing namespace and
  removed the P2M export and reactivation commands. Used `Finset.prod_le_prod₀` for the
  ordered product bound, updated deprecated Mathlib names and imports, and removed a redundant
  `try`. Omitted private lemmas unused by the kernel identity.
