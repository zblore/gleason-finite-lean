/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.LinearAlgebra.Trace

public section

/-!
# The definitions used in the statement

Kim Morrison's definitions from lean-eval's `gleason_theorem_finite` (`ChallengeDeps.lean` in
`leanprover/lean-eval`). `Challenge.lean` repeats them word for word, because Palomar only lets the
Challenge import Mathlib. The proof imports them from here. Comparator checks that the two copies
agree.
-/

namespace LeanEval
namespace Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An orthogonal projection on `H`: a self-adjoint idempotent continuous linear map. -/
@[expose] def IsOrthProj (P : H →L[ℂ] H) : Prop :=
  IsIdempotentElem P ∧ IsSelfAdjoint P

/-- A frame function on the projection lattice: non-negative on orthogonal projections,
finitely additive on orthogonal pairs, and `μ I = 1`. (In finite dimensions any countable
orthogonal family is finite, so finite additivity already yields countable additivity.) -/
structure FrameFunction (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  μ : (H →L[ℂ] H) → ℝ
  nonneg : ∀ P : H →L[ℂ] H, IsOrthProj P → 0 ≤ μ P
  additive : ∀ P Q : H →L[ℂ] H, IsOrthProj P → IsOrthProj Q → P * Q = 0 →
    μ (P + Q) = μ P + μ Q
  normalized : μ (1 : H →L[ℂ] H) = 1

/-- The real part of the complex trace of a continuous linear operator on a
finite-dimensional complex inner product space. -/
@[expose] noncomputable def reTr [FiniteDimensional ℂ H] (A : H →L[ℂ] H) : ℝ :=
  (LinearMap.trace ℂ H A.toLinearMap).re

end Analysis
end LeanEval
