import Probes.ActualSecondaryFiniteTensorIdentity

/-! Smoothness of the actual opposite mean follows from its same physical
coefficient. This finite real-bilinear expression never differentiates an
inactive phase separately. -/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep Label Sub : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [Fintype Label] [DecidableEq Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
private local instance oppositeTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance oppositeTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance oppositeTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace

 theorem actual_primary_opposite_mean_contDiffOn
    (phi : Label → Ep → D → ℝ) (tau : ℝ) (chi : Label → Ep → Sub → D → ℝ)
    (P Q : Label → Ep → Sub → D → V) (O : Set X)
    (hc : ∀ nu, ContDiffOn ℝ ∞ (fun z => incrementsSecondaryPhysicalCoefficient
      phi tau chi P Q (fun i _ => EuclideanSpace.single i 1) z nu) O) :
    ContDiffOn ℝ ∞ (actualPrimaryOppositeMeanTensor phi tau chi P Q) O := by
  have hcoeff : ContDiffOn ℝ ∞ (fun z => incrementsSecondaryPhysicalCoefficient
      phi tau chi P Q (fun i _ => EuclideanSpace.single i 1) z) O := contDiffOn_pi.2 hc
  apply actualRealTensorAssembly.contDiff.comp_contDiffOn
  apply contDiffOn_pi.2
  intro i
  apply contDiffOn_pi.2
  intro j
  simpa only [Function.comp_def,incrementsMeanBilinear_diagonal] using
    ((incrementsMeanBilinear (Λ := Label) (N := N) i j).contDiff.comp_contDiffOn hcoeff).clm_apply hcoeff

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_primary_opposite_mean_contDiffOn
