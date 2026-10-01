module

public import GleasonFinite

public section

/-!
# Gleason's theorem in finite dimensions, proved

The same statement as `Challenge.lean`, proved from the matrix theorem in `GleasonFinite.Gleason`
through the operator-to-matrix bridge in `GleasonFinite.Bridge`.
-/

open LeanEval.Analysis

theorem gleason_theorem_finite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [FiniteDimensional ℂ H]
    (hdim : 3 ≤ Module.finrank ℂ H)
    (f : FrameFunction H) :
    ∃! ρ : H →L[ℂ] H,
      ContinuousLinearMap.IsPositive ρ ∧
      reTr ρ = 1 ∧
      ∀ P : H →L[ℂ] H, IsOrthProj P → f.μ P = reTr (ρ * P) := by
  exact GleasonFinite.gleason_of_matrix hdim f
