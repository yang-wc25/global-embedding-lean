import NormalPolar.JointSecondaryGroupedDifferenceNative
import NormalPolar.JointBackgroundGroupedOriginalNorm

/-! The actual grouped forcing difference is controlled in the unchanged
original source-first atlas norm. The explicit cost precedes both external
parameters. It is computed from primitive reconstructed sources, including
all joint native derivatives and every original within-label cross term. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
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
local notation "IM" => 𝓘(ℝ,D)

theorem jointMixed_grouped_original_mean_difference_raw_norm
    (label : (Fin r × Bool) ↪ Fin p)
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → P → D → M)
    (chi : (l : Fin r) → Sub l → P × D → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : P) → (x : D) →
      normalSpace (I := IM) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (P × M) (P × D))
    (ha : ∀ l s, Round3ParameterChartPreserves (a l s)) (n length j : ℕ) (horder : j+2+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hMphase : 0 ≤ Mphase)
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep) (hA : IsSmoothBufferedAtlas A)
    (Samples : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (Omega : Fin A.count × Fin count → Set X) (hOmega : ∀ idx, IsOpen (Omega idx))
    (hOmegaSub : ∀ idx, Omega idx ⊆ (B idx.2).target ×ˢ (A.chart idx.1).target)
    (hSamples : ∀ idx, (parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx ⊆ Omega idx)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (phase : Fin r → P × M → ℝ)
    (profiles : ∀ idx, JointGroupedPrescribedParameterChartRawData F hF c chi nu phase a
      (B idx.2) (A.chart idx.1) (Omega idx) ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx)
      n j ell Mg Bchi Bnu Mphase T) :
    let vf := fun l s b x => (-(delta*tau)/(weight l)^2) • (chi l s (b,x) • nu l s b x)
    let mean := fun u b x => jointGroupedParameterPrescribedMean label F hF c vf phase tau length a u b x
    let C := ((j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j)*
      jointGroupedPrescribedMeanUniformCost Sub m N p n length j T weight Mg Bchi Bnu Mphase 1
    ∀ u v : Fin p → ℝ,
      (∀ idx, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B (fun b x => mean u b x-mean v b x) idx)
        ((parameterTensorModelEquiv (m+1) d).symm ⁻¹' Omega idx)) ∧
      paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B (fun b x => mean u b x-mean v b x))
        (incrementsOriginalDifferentiation A B) Samples ≠ ⊤ ∧
      (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B (fun b x => mean u b x-mean v b x))
        (incrementsOriginalDifferentiation A B) Samples).toReal ≤
        C*delta^2*(‖u‖+‖v‖)*‖u-v‖ := by
  intro vf mean C u v
  let Cmean := jointGroupedPrescribedMeanUniformCost Sub m N p n length j T weight Mg Bchi Bnu Mphase 1
  let cost := fun co : Fin ((m+1)*(m+1)) =>
    2^j*‖incrementsMeanBilinear (Λ := Fin r) (N := N) (finProdFinEquiv.symm co).1 (finProdFinEquiv.symm co).2‖*
      (∑ l, (Fintype.card (Sub l) : ℝ)*actualVariablePrescribedCoefficientCost m N p n length j
        T (weight l) Mg Bchi Bnu Mphase 1)^2
  have hcC (co) : cost co ≤ Cmean :=
    jointGroupedPrescribedMeanUniformCost_component Sub m N p n length j T weight
      Mg Bchi Bnu Mphase 1 (finProdFinEquiv.symm co).1 (finProdFinEquiv.symm co).2
  have hCmean : 0 ≤ Cmean := jointGroupedPrescribedMeanUniformCost_nonneg Sub m N p n length j
    T weight Mg Bchi Bnu Mphase 1
  let coeff := fun (idx : Fin A.count × Fin count) (z : X) (co : Fin ((m+1)*(m+1))) =>
    let w := fun k => mfderiv 𝓘(ℝ,D) IM (A.chart idx.1).symm z.2
      ((tangentSpaceCastModel 𝓘(ℝ,D) z.2).symm (EuclideanSpace.single k 1))
    mean u ((B idx.2).symm z.1) ((A.chart idx.1).symm z.2)
        (w (finProdFinEquiv.symm co).1) (w (finProdFinEquiv.symm co).2)-
      mean v ((B idx.2).symm z.1) ((A.chart idx.1).symm z.2)
        (w (finProdFinEquiv.symm co).1) (w (finProdFinEquiv.symm co).2)
  have hraw (idx : Fin A.count × Fin count) (co : Fin ((m+1)*(m+1))) :=
    jointGrouped_prescribed_parameter_chart_mean_difference_from_raw label F hF c chi nu phase a ha
      (B idx.2) (A.chart idx.1) (hA.chart_mem idx.1) (Omega idx)
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx) (hOmega idx) (hSamples idx)
      (hOmegaSub idx) n length j horder tau ell delta weight Mg Bchi Bnu Mphase
      htau htaul hell1 hMg hdelta hBchi hBnu hMphase T hT (profiles idx)
      (finProdFinEquiv.symm co).1 (finProdFinEquiv.symm co).2 u v
  have hout := actual_original_tensor_norm_of_real_germs A B (fun b x => mean u b x-mean v b x)
    Samples Omega hOmega hOmegaSub hSamples coeff (fun idx co => (hraw idx co).1)
    (fun _ _ _ => rfl) j ell (Cmean*delta^2*(‖u‖+‖v‖)*‖u-v‖)
    (htau.trans_le htaul) hell1 (by positivity) (by
      intro idx co k hk z hz
      exact ((hraw idx co).2 k hk z hz).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hcC co) (sq_nonneg delta))
            (add_nonneg (norm_nonneg u) (norm_nonneg v))) (norm_nonneg (u-v))))
  exact ⟨hout.1,hout.2.1,hout.2.2.trans_eq (by dsimp only [C,Cmean]; ring)⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointMixed_grouped_original_mean_difference_raw_norm
