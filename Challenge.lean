module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.LinearAlgebra.Trace

public section

/-!
# Gleason's theorem in finite dimensions

Let `H` be a finite-dimensional complex Hilbert space of dimension at least 3. A frame function
assigns a real number to each orthogonal projection on `H`. It is non-negative, additive on
orthogonal pairs, and sends the identity to 1. Gleason's theorem says every frame function has the
form `P ↦ Re Tr(ρ P)` for exactly one positive operator `ρ` with `Re Tr ρ = 1`, a density operator.
So a probability assignment on the quantum yes/no questions of `H` is the Born rule for a unique
quantum state.

The statement and the three definitions below are Kim Morrison's, from the problem
`gleason_theorem_finite` in lean-eval (`leanprover/lean-eval`). They are unchanged apart from the
module header, `@[expose]` on the two definitions, and moving the definitions into this file from
lean-eval's `ChallengeDeps.lean`.

In finite dimensions finite additivity on orthogonal pairs gives additivity on every orthogonal
family, so this is Gleason's original hypothesis. The theorem fails in dimension 2.
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

open LeanEval.Analysis

/-- **Gleason's theorem**, finite-dimensional version. For `dim H ≥ 3`, every frame
function on the projection lattice of `H` is given by `P ↦ re Tr(ρ P)` for the unique
density operator `ρ` (positive, `re Tr ρ = 1`). -/
theorem gleason_theorem_finite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [FiniteDimensional ℂ H]
    (hdim : 3 ≤ Module.finrank ℂ H)
    (f : FrameFunction H) :
    ∃! ρ : H →L[ℂ] H,
      ContinuousLinearMap.IsPositive ρ ∧
      reTr ρ = 1 ∧
      ∀ P : H →L[ℂ] H, IsOrthProj P → f.μ P = reTr (ρ * P) := by
  sorry
