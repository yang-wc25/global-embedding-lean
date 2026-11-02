import Probes.ActualSecondaryTensorResidual
import Probes.ActualSecondaryMetricIdentity

/-!
# The remodulated tensor is the SAME physical sine/cosine error

This exact identity contains the literal scalar first variation of the
original induced metric, evaluated on the actual constructed displacement.
No differentiability or residual estimate is postulated to define the error.
The physical smoothness and quantitative bounds are supplied by the preceding
finite-mode theorems.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Manifold Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Source" => Fin (m+1) → Fin (m+1) → ℝ

theorem actual_secondary_real_physical_residual_basis
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (chart : Ep → OpenPartialHomeomorph M D) (hR hI : X → Source)
    (tau : ℝ) (length : ℕ) (z : X) (i j : Fin (m+1)) :
    actualRemodulatedPhysicalTensor
      (actualSecondaryPhysicalError F hF chart hR hI tau length) (fun y : X => y.2 0) tau z
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      incrementsCoordinateMetricVariation (F z.1 ∘ (chart z.1).symm)
        (fun x => actualSecondaryWave F hF (fun p => (chart p).symm) hR hI
          (fun y : X => y.2 0) tau length (z.1, x)) z.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
      (Complex.exp (((z.2 0 / tau : ℝ) : ℂ) * Complex.I) *
        ((hR z i j : ℂ) + Complex.I * (hI z i j : ℂ))).re := by
  rw [actualRemodulatedPhysicalTensor_basis]
  unfold actualSecondaryPhysicalError
  dsimp only
  rw [actual_complex_demodulated_residual_real]
  congr 1
  apply congrArg (fun f : D → V => incrementsCoordinateMetricVariation
    (F z.1 ∘ (chart z.1).symm) f z.2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
  funext x
  have he := congrFun (actualSecondaryComplexRealWave_eq F hF (fun p => (chart p).symm)
    hR hI (fun y : X => y.2 0) tau length) (z.1, x)
  exact he

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_real_physical_residual_basis
