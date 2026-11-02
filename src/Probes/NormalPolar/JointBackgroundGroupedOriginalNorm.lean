import NormalPolar.JointSecondaryGroupedParameterRaw
import NormalPolar.JointSecondaryGroupedMeanCost
import NormalPolar.ParameterDisplacementPrescribedVariableOriginalMean
import NormalPolar.ParameterDisplacementRealTensorNorm
import Probes.Round4PrescribedOriginalMeanNorm

/-! All ordered components of the same original-label grouped prescribed
mean give its unchanged original source-first paper norm. Every parameter
direction is retained; the source and parameter samples and differentiation
domains are not replaced. The estimate is supplied by primitive raw sources. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {M P : Type*} {m N d p r count : ℕ}
  [TopologicalSpace P] [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
variable {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem jointBackground_grouped_original_mean_raw_norm
    (label : (Fin r × Bool) ↪ Fin p)
    (F : P → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → P → D → M)
    (chi : (l : Fin r) → Sub l → P × D → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : P) → (x : D) →
      normalSpace (I := 𝓙) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (P × M) (P × D))
    (ha : ∀ l s, Round3ParameterChartPreserves (a l s)) (n length j : ℕ) (horder : j+2+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase Ku : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hMphase : 0 ≤ Mphase) (hKu : 0 ≤ Ku)
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep) (hA : IsSmoothBufferedAtlas A)
    (Samples : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (Omega : Fin A.count × Fin count → Set X) (hOmega : ∀ idx, IsOpen (Omega idx))
    (hOmegaSub : ∀ idx, Omega idx ⊆ (B idx.2).target ×ˢ (A.chart idx.1).target)
    (hSamples : ∀ idx, (parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx ⊆ Omega idx)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (phase : Fin r → P × M → ℝ)
    (profiles : ∀ idx, JointGroupedPrescribedParameterChartRawData F hF c chi nu phase a
      (B idx.2) (A.chart idx.1) (Omega idx) ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx)
      n j ell Mg Bchi Bnu Mphase T)
    (u : P → Fin p → ℝ)
    (hu : ∀ idx, ContDiffOn ℝ ∞ (fun z : X => u ((B idx.2).symm z.1)) (Omega idx))
    (hub : ∀ idx k, k ≤ j → ∀ z : X, parameterTensorModelEquiv (m+1) d z ∈ Samples idx →
      ell^k*‖iteratedFDeriv ℝ k (fun z : X => u ((B idx.2).symm z.1)) z‖ ≤ Ku) :
    let vf := fun l s b x => (-(delta*tau)/(weight l)^2) • (chi l s (b,x) • nu l s b x)
    let mean := fun b x => jointGroupedParameterPrescribedMean label F hF c vf phase tau length a (u b) b x
    let C := jointGroupedPrescribedMeanUniformCost Sub m N p n length j T weight Mg Bchi Bnu Mphase Ku
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
      (∑ l, (Fintype.card (Sub l) : ℝ)*actualVariablePrescribedCoefficientCost m N p n length j T (weight l) Mg Bchi Bnu Mphase Ku)^2
  have hc (co) : 0 ≤ cost co := mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) j)
    (ContinuousLinearMap.opNorm_nonneg _)) (sq_nonneg _)
  have hcC (co) : cost co ≤ C :=
    jointGroupedPrescribedMeanUniformCost_component Sub m N p n length j T weight
      Mg Bchi Bnu Mphase Ku (finProdFinEquiv.symm co).1 (finProdFinEquiv.symm co).2
  let coeff := fun (idx : Fin A.count × Fin count) (z : X) (co : Fin ((m+1)*(m+1))) =>
    let w := fun k => mfderiv 𝓘(ℝ,D) 𝓙 (A.chart idx.1).symm z.2
      ((tangentSpaceCastModel 𝓘(ℝ,D) z.2).symm (EuclideanSpace.single k 1))
    mean ((B idx.2).symm z.1) ((A.chart idx.1).symm z.2)
      (w (finProdFinEquiv.symm co).1) (w (finProdFinEquiv.symm co).2)
  have hraw (idx : Fin A.count × Fin count) (co : Fin ((m+1)*(m+1))) :=
    jointGrouped_prescribed_parameter_chart_mean_from_raw label F hF c chi nu phase a ha (B idx.2) (A.chart idx.1)
      (hA.chart_mem idx.1) (Omega idx) ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx)
      (hOmega idx) (hSamples idx) (hOmegaSub idx) n length j horder tau ell delta weight Mg Bchi Bnu Mphase Ku
      htau htaul hell1 hMg hdelta hBchi hBnu hMphase hKu T hT (profiles idx) u (hu idx) (hub idx)
      (finProdFinEquiv.symm co).1 (finProdFinEquiv.symm co).2
  have hout := actual_original_tensor_norm_of_real_germs A B mean Samples Omega hOmega hOmegaSub hSamples
    coeff (fun idx co => (hraw idx co).1) (fun _ _ _ => rfl) j ell (C*delta^2) (htau.trans_le htaul) hell1
    (mul_nonneg (jointGroupedPrescribedMeanUniformCost_nonneg Sub m N p n length j T weight Mg Bchi Bnu Mphase Ku) (sq_nonneg delta))
    (fun idx co k hk z hz => ((hraw idx co).2 k hk z hz).trans (mul_le_mul_of_nonneg_right (hcC co) (sq_nonneg delta)))
  exact ⟨hout.1,hout.2.1,hout.2.2.trans_eq (by ring)⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointBackground_grouped_original_mean_raw_norm
