import Probes.ActualSecondaryRealPhysicalIdentity
import Probes.ActualSecondaryTensorNaturality

/-!
# Whole bilinear identity for the actual physical secondary error

The genuine physical error is identified in all tangent directions. The
right hand side is the native first variation of the SAME actual wave minus
the original remodulated forcing tensor. This is the identity subsequently
transported between actual source charts.
-/

noncomputable section
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

def actualSecondaryLocalForcingTensor (hR hI : X → Source) (tau : ℝ) :
    X → D →L[ℝ] D →L[ℝ] ℝ := fun z =>
  actualRealTensorAssembly (fun i j => Complex.exp (((z.2 0 / tau : ℝ) : ℂ) * Complex.I) *
    ((hR z i j : ℂ) + Complex.I * (hI z i j : ℂ)))

theorem actual_secondary_physical_tensor_eq_linearization
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (chart : Ep → OpenPartialHomeomorph M D) (hR hI : X → Source)
    (tau : ℝ) (length : ℕ) (z : X)
    (hFc : DifferentiableAt ℝ (F z.1 ∘ (chart z.1).symm) z.2)
    (hWave : DifferentiableAt ℝ (fun x => actualSecondaryWave F hF
      (fun p => (chart p).symm) hR hI (fun y : X => y.2 0) tau length (z.1,x)) z.2) :
    actualRemodulatedPhysicalTensor
      (actualSecondaryPhysicalError F hF chart hR hI tau length) (fun y : X => y.2 0) tau z =
      actualCoordinateMetricLinearization (F z.1 ∘ (chart z.1).symm)
        (fun x => actualSecondaryWave F hF (fun p => (chart p).symm) hR hI
          (fun y : X => y.2 0) tau length (z.1,x)) z.2 -
      actualSecondaryLocalForcingTensor hR hI tau z := by
  apply actual_bilinear_tensor_eq_of_basis
  intro i j
  rw [actual_secondary_real_physical_residual_basis]
  simp only [sub_apply, actualSecondaryLocalForcingTensor, actualRealTensorAssembly_basis]
  rw [actual_coordinate_metric_linearization_eq_variation _ _ _ _ _ hFc hWave]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_physical_tensor_eq_linearization
