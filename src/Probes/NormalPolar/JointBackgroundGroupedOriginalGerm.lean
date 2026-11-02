import NormalPolar.JointBackgroundGroupedOriginalNorm
import Smoothing.ParameterRound2TensorGermSpace

/-! One global grouped original-label parameter field, assembled through its
canonical chart pullbacks, is an honest original symmetric tensor germ. The
whole original joint seminorm and its normalized bound are derived from the
same primitive sources, uniformly across all parameter charts. -/

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

theorem jointBackground_grouped_original_mean_raw_germ
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
      ell^k*‖iteratedFDeriv ℝ k (fun z : X => u ((B idx.2).symm z.1)) z‖ ≤ Ku)
    (W : Set (P × M)) (hCompact : ∀ idx, IsCompact (Samples idx))
    (hOrig : ∀ idx, Samples idx ⊆ incrementsOriginalDifferentiation A B idx)
    (hdelta0 : delta ≠ 0) :
    let vf := fun l s b x => (-(delta*tau)/(weight l)^2) • (chi l s (b,x) • nu l s b x)
    let mean := fun b x => jointGroupedParameterPrescribedMean label F hF c vf phase tau length a (u b) b x
    let C := ((j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j)*
      jointGroupedPrescribedMeanUniformCost Sub m N p n length j T weight Mg Bchi Bnu Mphase Ku
    let pnorm := parameterRound2_originalTensorGermSeminorm A B Samples W hCompact hOrig ell j
    ∃ probe : parameterRound2_originalTensorGermSpace A B Samples W,
      probe.val = mean ∧ pnorm probe ≤ C*delta^2 ∧ pnorm ((delta^2)⁻¹ • probe) ≤ C := by
  intro vf mean C pnorm
  have hnorm := jointBackground_grouped_original_mean_raw_norm label F hF c chi nu a ha
    n length j horder tau ell delta weight Mg Bchi Bnu Mphase Ku htau htaul hell1
    hMg hdelta hBchi hBnu hMphase hKu A B hA Samples Omega hOmega hOmegaSub hSamples
    T hT phase profiles u hu hub
  have hmem : mean ∈ parameterRound2_originalTensorGermSpace A B Samples W := by
    constructor
    · intro idx
      refine ⟨(parameterTensorModelEquiv (m+1) d).symm ⁻¹' Omega idx,
        (hOmega idx).preimage (parameterTensorModelEquiv (m+1) d).symm.continuous,?_,hnorm.1 idx⟩
      intro y hy
      apply hSamples idx
      change parameterTensorModelEquiv (m+1) d ((parameterTensorModelEquiv (m+1) d).symm y) ∈ Samples idx
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy
    · intro z _
      exact jointGroupedParameterPrescribedMean_isSymm label F hF c vf phase tau length a (u z.1) z.1 z.2
  let probe : parameterRound2_originalTensorGermSpace A B Samples W := ⟨mean,hmem⟩
  have hb : pnorm probe ≤ C*delta^2 := hnorm.2.2
  refine ⟨probe,rfl,hb,?_⟩
  calc
    pnorm ((delta^2)⁻¹ • probe) = (delta^2)⁻¹*pnorm probe := by
      rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg delta))]
    _ ≤ (delta^2)⁻¹*(C*delta^2) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (sq_nonneg delta))
    _ = C := by field_simp

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointBackground_grouped_original_mean_raw_germ
