import NormalPolar.JointBackgroundGroupedPrescribedGerm
import NormalPolar.PassiveOriginalSmallParameter

/-! A produced small grouped prescribed forcing on the whole physical parameter
manifold. The parameter is one actual global chart cutoff, fixed with its
all-order profile before ell, tau or delta. Its zero profile is the actual
small amplitude chosen from the primitive source cost and reserve, so the
normalized forcing reserve is proved rather than supplied as a hypothesis.
The initial buffer choice leaves every native chart and norm sample literal. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {m N d r : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [T2Space P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
variable {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1))
local notation "𝓙" => 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))

theorem jointBackground_grouped_small_actual_prescribed_forcing
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (Q : Fin B.count → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (Samples : Fin A.count × Fin B.count → Set (Fin (m+1+d) → ℝ))
    (hCompact : ∀ idx, IsCompact (Samples idx))
    (hOrig : ∀ idx, Samples idx ⊆ incrementsOriginalDifferentiation A B.chart idx)
    (hSQ : ∀ idx z, parameterTensorModelEquiv (m+1) d z ∈ Samples idx → z.1 ∈ Q idx.2)
    (n : ℕ → ℕ) (length : ℕ) (horder : ∀ j, j+2+length ≤ n j)
    (T : ℕ → ℕ → ℝ) (hT : ∀ j k, 0 ≤ T j k)
    (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase : ℕ → ℝ)
    (hMg : ∀ j, 0 ≤ Mg j) (hBchi : ∀ j, 0 ≤ Bchi j)
    (hBnu : ∀ j, 0 ≤ Bnu j) (hMphase : ∀ j, 0 ≤ Mphase j)
    (rho : ℝ) (hrho : 0 < rho) :
    let Csrc := jointGroupedPrescribedZeroSourceCost Sub m N d d (n 0) length (T 0) weight
      (Mg 0) (Bchi 0) (Bnu 0) (Mphase 0)
    let amplitude := passiveOriginalReserveAmplitude Csrc rho
    let u := passiveOriginalSmallParameter B amplitude
      (passiveOriginalReserveAmplitude_pos Csrc rho hrho) b p₀
    ∃ Ku : ℕ → ℝ, (∀ j, 0 ≤ Ku j) ∧ Ku 0 = amplitude ∧
      let C := fun j => ((j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j)*
        jointGroupedPrescribedMeanUniformCost Sub m N d (n j) length j (T j) weight
          (Mg j) (Bchi j) (Bnu j) (Mphase j) (Ku j)
      ∀ (label : (Fin r × Bool) ↪ Fin d)
        (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
        (c : (l : Fin r) → Sub l → P → D → M)
      (chi : (l : Fin r) → Sub l → P × D → ℝ)
        (nu : (l : Fin r) → (s : Sub l) → (p : P) → (x : D) →
        normalSpace (I := 𝓙) (F p) (c l s p x))
        (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (P × M) (P × D))
        (ha : ∀ l s, Round3ParameterChartPreserves (a l s)) (phase : Fin r → P × M → ℝ)
        (tau ell delta : ℝ), 0 < tau → tau ≤ ell → ell ≤ 1 → 0 < delta →
      ∀ (Omega : ℕ → Fin A.count × Fin B.count → Set X)
        (hOmega : ∀ j idx, IsOpen (Omega j idx))
        (hOmegaSub : ∀ j idx, Omega j idx ⊆ (B.chart idx.2).target ×ˢ (A.chart idx.1).target)
        (hSamples : ∀ j idx, (parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx ⊆ Omega j idx)
        (profiles : ∀ j idx, JointGroupedPrescribedParameterChartRawData F hF c chi nu phase a
          (B.chart idx.2) (A.chart idx.1) (Omega j idx)
          ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx)
          (n j) j ell (Mg j) (Bchi j) (Bnu j) (Mphase j) (T j)),
      let vf := fun l s p x => (-(delta*tau)/(weight l)^2) • (chi l s (p,x) • nu l s p x)
      let mean := fun p x => jointGroupedParameterPrescribedMean label F hF c vf phase tau length a (u p) p x
      let pj := parameterRound2_originalTensorGermSeminorm A B.chart Samples univ hCompact hOrig ell
      ∃ probe Pforce : parameterRound2_originalTensorGermSpace A B.chart Samples univ,
        probe.val = mean ∧ Pforce = (delta^2)⁻¹ • probe ∧
        Pforce.val = (delta^2)⁻¹ • mean ∧
        (∀ j, pj j probe ≤ C j*delta^2) ∧ (∀ j, pj j Pforce ≤ C j) ∧
        pj 0 Pforce ≤ rho/4 := by
  intro Csrc amplitude u
  obtain ⟨huSmooth,Ku,hKu,hKu0,hu,hjets⟩ := passiveOriginalSmallParameter_joint_profiles (Es := D)
    B hB Q hQ hQT amplitude (passiveOriginalReserveAmplitude_pos Csrc rho hrho) b p₀ hp₀
  have hsmall : Csrc*(Ku 0)^2 ≤ rho/4 := by
    rw [hKu0]
    exact passiveOriginalReserveAmplitude_small Csrc rho hrho
  refine ⟨Ku,hKu,hKu0,?_⟩
  intro C label F hF c chi nu a ha phase tau ell delta htau htaul hell1 hdelta
    Omega hOmega hOmegaSub hSamples profiles vf mean pj
  have huOmega : ∀ j idx, ContDiffOn ℝ ∞ (fun z : X => u ((B.chart idx.2).symm z.1))
      (Omega j idx) := by
    intro j idx
    exact (hu idx.2).mono (fun _ hz => (hOmegaSub j idx hz).1)
  have hub : ∀ j idx k, k ≤ j → ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ Samples idx →
      ell^k*‖iteratedFDeriv ℝ k (fun z : X => u ((B.chart idx.2).symm z.1)) z‖ ≤ Ku j := by
    intro j idx k hk z hz
    exact hjets j ell (htau.trans_le htaul).le hell1 k hk idx.2 z (hSQ idx z hz)
  exact jointBackground_grouped_actual_prescribed_all_order_germ A B.chart hA Samples hCompact hOrig
    n length horder T hT weight Mg Bchi Bnu Mphase Ku hMg hBchi hBnu hMphase hKu rho hsmall
    label F hF c chi nu a ha phase tau ell delta htau htaul hell1 hdelta
    Omega hOmega hOmegaSub hSamples profiles u huOmega hub

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointBackground_grouped_small_actual_prescribed_forcing
