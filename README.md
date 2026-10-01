# gleason-finite-lean

[![CI](https://github.com/zblore/gleason-finite-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/zblore/gleason-finite-lean/actions/workflows/ci.yml)

Gleason's theorem in finite dimensions, machine-checked in Lean 4. For a complex Hilbert space of
dimension at least 3, every frame function on the orthogonal projections is P ↦ Re Tr(ρP) for a
unique positive operator ρ with trace 1.

The statement in `Challenge.lean` is Kim Morrison's lean-eval problem `gleason_theorem_finite`,
unchanged. Palomar only lets the Challenge import Mathlib, so I moved lean-eval's three definitions
into it and added the module header.

The proof comes from my [csd-lean4](https://github.com/zblore/csd-lean4) repository (commit
`4b396fa3`), where I proved Gleason's theorem for matrices on ℂᴺ following Cooke, Keane and Moran
(1985). `GleasonFinite/Gleason` holds those files. `GleasonFinite/Bridge.lean` takes matrices in an
orthonormal basis to turn the operator statement into the matrix one.

Checks: CI runs `lake comparator` the way Palomar does, with Lean's kernel, nanoda and con-ron. The
proof uses only `propext`, `Classical.choice` and `Quot.sound`.
[lean-eval-gleason](https://github.com/zblore/lean-eval-gleason) holds the same proof in lean-eval's
layout, where lean-eval's own Comparator setup accepts it.

This isn't the first Lean proof of finite-dimensional Gleason.
[Bobart0/gleason-theorem-lean](https://github.com/Bobart0/gleason-theorem-lean) proves the same case
by the same route, and [markkasaurus/gleason-theorem-lean](https://github.com/markkasaurus/gleason-theorem-lean)
proves the separable case.

I drafted the Lean with Claude Code. Fable 5.1 and Astra reviewed the Gleason proof in csd-lean4
before I carved it out.
