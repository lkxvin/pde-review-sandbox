import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.FinCases

/-!
# Orthogonal invariance of the Laplacian

`Δ(u ∘ A) = (Δu) ∘ A` for a linear isometry `A` of a finite-dimensional real inner product
space: the Laplacian is the trace of the Hessian, and an orthonormal basis is mapped by `A`
to an orthonormal basis.  Consequently rotations/reflections of a domain carry harmonic
functions to harmonic functions (`isHarmonic_comp_linearIsometryEquiv`), the symmetry
principle behind "Dirichlet problem on a square/regular polygon" computations.
-/

open InnerProductSpace Laplacian

namespace Laplace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Orthogonal invariance of the Laplacian:** `Δ(u ∘ A)(x) = (Δu)(A x)`. -/
theorem laplacian_comp_linearIsometryEquiv (u : E → ℝ) (A : E ≃ₗᵢ[ℝ] E) (x : E) :
    Δ (u ∘ A) x = Δ u (A x) := by
  set b := stdOrthonormalBasis ℝ E with hb
  have h1 := congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis (u ∘ A) b) x
  have h2 := congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis u (b.map A)) (A x)
  rw [h1, h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcomp := A.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right u uniqueDiffOn_univ
    (Set.mem_univ (A.toContinuousLinearEquiv x)) 2
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at hcomp
  have hfun : (u ∘ A) = u ∘ A.toContinuousLinearEquiv := rfl
  rw [hfun, hcomp, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext j
  fin_cases j <;> simp [OrthonormalBasis.map_apply]

/-- Harmonic functions are carried to harmonic functions by linear isometries. -/
theorem laplacian_comp_linearIsometryEquiv_eq_zero {u : E → ℝ} (A : E ≃ₗᵢ[ℝ] E) {x : E}
    (h : Δ u (A x) = 0) : Δ (u ∘ A) x = 0 := by
  rw [laplacian_comp_linearIsometryEquiv, h]

end Laplace
