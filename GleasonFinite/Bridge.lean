/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import GleasonFinite.Defs
public import GleasonFinite.Gleason.Core
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# From operators on `H` to matrices, and back

lean-eval states Gleason's theorem for operators on a finite-dimensional complex Hilbert space
`H` (`LeanEval.Analysis.FrameFunction`, `IsOrthProj`, `reTr`). The proof in `GleasonFinite.Gleason`
is for matrices on `ℂᴺ` (`Gleason.ProjectionPackage`). This file connects the two.

Fix the standard orthonormal basis of `H`. Taking matrices in that basis is a star-algebra
isomorphism `toMat` from operators to `N × N` matrices, where `N = finrank ℂ H`. Under it:

* orthogonal projections correspond to star projections (`isOrthProj_iff`),
* `reTr` is the real part of the matrix trace (`reTr_eq`),
* positive operators correspond to positive semidefinite matrices (`isPositive_iff`).

So a frame function on `H` becomes a projection package on matrices (`framePackage`), the
matrix theorem applies, and existence and uniqueness transfer back (`gleason_of_matrix`).
-/

open LeanEval.Analysis Module
open scoped ComplexOrder

namespace GleasonFinite

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- Matrices of operators in the standard orthonormal basis of `H`, as a star-algebra
isomorphism. -/
noncomputable def toMat :
    (H →L[ℂ] H) ≃⋆ₐ[ℂ] Matrix (Fin (finrank ℂ H)) (Fin (finrank ℂ H)) ℂ :=
  (({ LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ ↦ rfl
      map_star' := LinearMap.adjoint_toContinuousLinearMap } :
      (H →ₗ[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)).symm).trans
    (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H))

theorem toMat_apply (A : H →L[ℂ] H) :
    toMat A = LinearMap.toMatrix (stdOrthonormalBasis ℂ H).toBasis
      (stdOrthonormalBasis ℂ H).toBasis (A : H →ₗ[ℂ] H) :=
  rfl

/-- Orthogonal projections on `H` are exactly the operators whose matrix is a star projection. -/
theorem isOrthProj_iff (P : H →L[ℂ] H) : IsOrthProj P ↔ IsStarProjection (toMat P) := by
  constructor
  · rintro ⟨hidem, hsa⟩
    exact ⟨hidem.map toMat, hsa.map toMat⟩
  · rintro ⟨hidem, hsa⟩
    have h := toMat.symm_apply_apply P
    exact ⟨h ▸ hidem.map toMat.symm, h ▸ hsa.map toMat.symm⟩

/-- `reTr` is the real part of the trace of the matrix. -/
theorem reTr_eq (A : H →L[ℂ] H) : reTr A = ((toMat A).trace).re := by
  rw [reTr, toMat_apply, LinearMap.trace_eq_matrix_trace ℂ (stdOrthonormalBasis ℂ H).toBasis]

/-- An operator is positive exactly when its matrix is positive semidefinite. -/
theorem isPositive_iff (A : H →L[ℂ] H) :
    A.IsPositive ↔ (toMat A).PosSemidef := by
  rw [toMat_apply, LinearMap.posSemidef_toMatrix_iff,
    ContinuousLinearMap.isPositive_toLinearMap_iff]

/-- The trace of a Hermitian matrix is real. -/
theorem trace_eq_re_of_isHermitian {n : Type*} [Fintype n] {M : Matrix n n ℂ}
    (hM : M.IsHermitian) : M.trace = (M.trace.re : ℂ) := by
  refine (Complex.conj_eq_iff_re.mp ?_).symm
  change star M.trace = M.trace
  rw [← Matrix.trace_conjTranspose, hM.eq]

/-- A frame function on `H`, read through `toMat`, is a projection package on matrices. -/
noncomputable def framePackage (f : FrameFunction H) :
    Gleason.ProjectionPackage (finrank ℂ H) where
  p M := f.μ (toMat.symm M)
  nonneg M hM := f.nonneg _ ((isOrthProj_iff _).2 (by rwa [StarAlgEquiv.apply_symm_apply]))
  total_one := by rw [map_one]; exact f.normalized
  additive P Q hP hQ hPQ := by
    rw [map_add]
    refine f.additive _ _ ((isOrthProj_iff _).2 (by rwa [StarAlgEquiv.apply_symm_apply]))
      ((isOrthProj_iff _).2 (by rwa [StarAlgEquiv.apply_symm_apply])) ?_
    rw [← map_mul, hPQ, map_zero]

/-- Gleason's theorem in lean-eval's form, from the matrix theorem. -/
theorem gleason_of_matrix (hdim : 3 ≤ finrank ℂ H) (f : FrameFunction H) :
    ∃! ρ : H →L[ℂ] H,
      ContinuousLinearMap.IsPositive ρ ∧
      reTr ρ = 1 ∧
      ∀ P : H →L[ℂ] H, IsOrthProj P → f.μ P = reTr (ρ * P) := by
  obtain ⟨σ, ⟨hpsd, htr, hrep⟩, huniq⟩ := (framePackage f).gleason_representation hdim
  refine ⟨toMat.symm σ, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [isPositive_iff, StarAlgEquiv.apply_symm_apply]
    exact hpsd
  · rw [reTr_eq, StarAlgEquiv.apply_symm_apply, htr, Complex.one_re]
  · intro P hP
    have h := hrep (toMat P) ((isOrthProj_iff P).1 hP)
    simp only [framePackage, StarAlgEquiv.symm_apply_apply] at h
    rw [h, reTr_eq, map_mul, StarAlgEquiv.apply_symm_apply]
  · rintro ρ ⟨hpos, htr1, hrep'⟩
    have hpsdρ : (toMat ρ).PosSemidef := (isPositive_iff ρ).1 hpos
    have hσ : toMat ρ = σ := by
      refine huniq (toMat ρ) ⟨hpsdρ, ?_, ?_⟩
      · rw [trace_eq_re_of_isHermitian hpsdρ.1, ← reTr_eq, htr1, Complex.ofReal_one]
      · intro M hM
        have hP : IsOrthProj (toMat.symm M) :=
          (isOrthProj_iff _).2 (by rwa [StarAlgEquiv.apply_symm_apply])
        change f.μ (toMat.symm M) = _
        rw [hrep' _ hP, reTr_eq, map_mul, StarAlgEquiv.apply_symm_apply]
    rw [← hσ, StarAlgEquiv.symm_apply_apply]

end GleasonFinite
