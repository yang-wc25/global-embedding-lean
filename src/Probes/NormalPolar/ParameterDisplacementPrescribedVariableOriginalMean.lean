import NormalPolar.ParameterDisplacementPrescribedVariableNativeMean
import NormalPolar.ParameterDisplacementRealTensorNorm
import Probes.Round4PrescribedOriginalMeanNorm

/-! All ordered components of the same variable-parameter native prescribed
mean give its unchanged original source-first paper norm. Every parameter
direction is retained; the source and parameter samples and differentiation
domains are not replaced. The estimate is supplied by primitive raw sources. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {M : Type*} {m N d p r count : ℕ}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def actualVariablePrescribedMeanUniformCost (m N p n length j : ℕ)
    (T : ℕ → ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase Ku : ℝ) : ℝ :=
  ∑ co : Fin ((m+1)*(m+1)),
    2^j*‖incrementsMeanBilinear (Λ := Fin r) (N := N) (finProdFinEquiv.symm co).1 (finProdFinEquiv.symm co).2‖*
      (∑ l, actualVariablePrescribedCoefficientCost m N p n length j T (weight l) Mg Bchi Bnu Mphase Ku)^2

theorem actualVariablePrescribedMeanUniformCost_nonneg (m N p n length j : ℕ)
    (T : ℕ → ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase Ku : ℝ) :
    0 ≤ actualVariablePrescribedMeanUniformCost m N p n length j T weight Mg Bchi Bnu Mphase Ku := by
  apply Finset.sum_nonneg
  intro co _
  exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) j)
    (ContinuousLinearMap.opNorm_nonneg _)) (sq_nonneg _)

theorem actual_prescribed_variable_original_mean_raw_norm
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := 𝓙) (F b) (c l b x))
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (hW : IsOpen W) (n length j : ℕ) (horder : j+2+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase Ku : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hMphase : 0 ≤ Mphase) (hKu : 0 ≤ Ku)
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph Ep Ep) (hA : IsSmoothBufferedAtlas A)
    (Samples : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (Omega : Fin A.count × Fin count → Set X) (hOmega : ∀ idx, IsOpen (Omega idx))
    (hOmegaSub : ∀ idx, Omega idx ⊆ (B idx.2).target ×ˢ (A.chart idx.1).target)
    (hSamples : ∀ idx, (parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx ⊆ Omega idx)
    (hkappa : ∀ idx, ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (round4OriginalObserver A B idx) (Omega idx))
    (hmap : ∀ idx, MapsTo (round4OriginalObserver A B idx) (Omega idx) W)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (phase : Fin r → Ep × M → ℝ)
    (profiles : ∀ idx, ActualPrescribedObservationProfiles F hF c chi nu a W K n (j+1) ell Mg Bchi Bnu
      (round4OriginalObserver A B idx) (Omega idx) ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx) T phase Mphase)
    (u : Ep → Fin p → ℝ)
    (hu : ∀ idx, ContDiffOn ℝ ∞ (fun z : X => u ((B idx.2).symm z.1)) (Omega idx))
    (hub : ∀ idx k, k ≤ j → ∀ z : X, parameterTensorModelEquiv (m+1) d z ∈ Samples idx →
      ell^k*‖iteratedFDeriv ℝ k (fun z : X => u ((B idx.2).symm z.1)) z‖ ≤ Ku) :
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let mean := fun b x => round4PrescribedNativeMean label F hF c vf phase tau length a (u b) b x
    let C := actualVariablePrescribedMeanUniformCost m N p n length j T weight Mg Bchi Bnu Mphase Ku
    (∀ idx, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B mean idx)
      ((parameterTensorModelEquiv (m+1) d).symm ⁻¹' Omega idx)) ∧
    paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B mean)
      (incrementsOriginalDifferentiation A B) Samples ≠ ⊤ ∧
    (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B mean)
      (incrementsOriginalDifferentiation A B) Samples).toReal ≤
      ((j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*C)*delta^2 := by
  intro vf mean C
  let cost := fun co : Fin ((m+1)*(m+1)) =>
    2^j*‖incrementsMeanBilinear (Λ := Fin r) (N := N) (finProdFinEquiv.symm co).1 (finProdFinEquiv.symm co).2‖*
      (∑ l, actualVariablePrescribedCoefficientCost m N p n length j T (weight l) Mg Bchi Bnu Mphase Ku)^2
  have hc (co) : 0 ≤ cost co := mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) j)
    (ContinuousLinearMap.opNorm_nonneg _)) (sq_nonneg _)
  have hcC (co) : cost co ≤ C := Finset.single_le_sum (fun t _ => hc t) (Finset.mem_univ co)
  let coeff := fun (idx : Fin A.count × Fin count) (z : X) (co : Fin ((m+1)*(m+1))) =>
    let w := fun k => mfderiv 𝓘(ℝ,D) 𝓙 (A.chart idx.1).symm z.2
      ((tangentSpaceCastModel 𝓘(ℝ,D) z.2).symm (EuclideanSpace.single k 1))
    mean ((B idx.2).symm z.1) ((A.chart idx.1).symm z.2)
      (w (finProdFinEquiv.symm co).1) (w (finProdFinEquiv.symm co).2)
  have hraw (idx : Fin A.count × Fin count) (co : Fin ((m+1)*(m+1))) := actual_prescribed_variable_native_mean_from_raw
    label F hF c chi nu a W K hW n length j horder tau ell delta weight Mg Bchi Bnu Mphase Ku
    htau htaul hell1 hMg hdelta hBchi hBnu hMphase hKu
    (round4OriginalObserver A B idx) (Omega idx) ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx)
    (hOmega idx) (hSamples idx) (hkappa idx) (hmap idx) T hT phase (profiles idx)
    (fun z : X => u ((B idx.2).symm z.1)) (hu idx) (hub idx)
    (B idx.2).symm (A.chart idx.1) (hA.chart_mem idx.1) rfl (fun z hz => (hOmegaSub idx hz).2)
    (finProdFinEquiv.symm co).1 (finProdFinEquiv.symm co).2
  have hout := actual_original_tensor_norm_of_real_germs A B mean Samples Omega hOmega hOmegaSub hSamples
    coeff (fun idx co => (hraw idx co).1) (fun _ _ _ => rfl) j ell (C*delta^2) (htau.trans_le htaul) hell1
    (mul_nonneg (actualVariablePrescribedMeanUniformCost_nonneg m N p n length j T weight Mg Bchi Bnu Mphase Ku) (sq_nonneg delta))
    (fun idx co k hk z hz => ((hraw idx co).2 k hk z hz).trans (mul_le_mul_of_nonneg_right (hcC co) (sq_nonneg delta)))
  exact ⟨hout.1,hout.2.1,hout.2.2.trans_eq (by ring)⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_prescribed_variable_original_mean_raw_norm
