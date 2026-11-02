import NormalPolar.JointMixedParameterInitialization

/-! Initialization provides the full original ball and all joint parameter
jets without a circular buffer hypothesis. The primitive source cost fixes
the amplitude and initialized atlas first; the higher Ku sequence is then
chosen once, before every derivative scale. The global parameter function
is the same function already used by the true whole-family mean recurrence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Filter Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {d : ℕ} {P Es : Type*}
  [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Fin d → ℝ

theorem jointMixed_parameter_initialized_profiles
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (Q : Fin B.count → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (sourceCost rho : ℝ) (hrho : 0 < rho)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b) :
    let amplitude := passiveOriginalReserveAmplitude sourceCost rho
    let ha := passiveOriginalReserveAmplitude_pos sourceCost rho hrho
    let Initialized := jointMixedParameterInitializedAtlas B sourceCost rho hrho
    let u := passiveOriginalSmallParameter B amplitude ha b p₀
    IsSmoothBufferedAtlas Initialized ∧ sourceCost*amplitude^2 ≤ rho/4 ∧
      ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,X) ∞ u ∧ (∀ p, ‖u p‖ ≤ amplitude) ∧
      ∃ Ku : ℕ → ℝ, (∀ j, 0 ≤ Ku j) ∧ Ku 0 = amplitude ∧
        (∀ i, ContDiffOn ℝ ∞ (fun z : Ep × Es => u ((Initialized.chart i).symm z.1))
          (Prod.fst ⁻¹' (Initialized.chart i).target)) ∧
        (∀ j ell, 0 ≤ ell → ell ≤ 1 → ∀ k, k ≤ j → ∀ i z, z.1 ∈ Q i →
          ell^k * ‖iteratedFDeriv ℝ k
            (fun y : Ep × Es => u ((Initialized.chart i).symm y.1)) z‖ ≤ Ku j) ∧
        ∀ v : X, ‖v‖ < actualRepairParameterRadius (tensorChartFamilyOfAtlas Initialized) →
          u (actualRepairParameterMap (tensorChartFamilyOfAtlas Initialized) b p₀ v) = v := by
  intro amplitude ha Initialized u
  obtain ⟨hSmooth,Ku,hKu,hKu0,hNative,hjets⟩ :=
    passiveOriginalSmallParameter_joint_profiles (Es := Es) B hB Q hQ hQT amplitude ha b p₀ hp₀
  refine ⟨jointMixedParameterInitializedAtlas_smooth B hB sourceCost rho hrho,
    passiveOriginalReserveAmplitude_small sourceCost rho hrho,hSmooth,
    passiveOriginalSmallParameter_bound B amplitude ha b p₀,
    Ku,hKu,hKu0,hNative,hjets,?_⟩
  intro v hv
  change passiveOriginalSmallParameter B amplitude ha b p₀
    (actualRepairParameterMap (tensorChartFamilyOfAtlas Initialized) b p₀ v) = v
  rw [← jointMixedParameterInitializedAtlas_parameter B sourceCost rho hrho b p₀]
  exact passiveOriginalSmallParameter_original_ball_identity Initialized amplitude ha
    (jointMixedParameterInitializedAtlas_buffer B sourceCost rho hrho) b p₀ hp₀ v hv

theorem jointMixed_parameter_initialized_original_germ
    (B : BufferedAtlas P Ep) (sourceCost rho : ℝ) (hrho : 0 < rho)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (v : X) (hv : ‖v‖ < actualRepairParameterRadius
      (tensorChartFamilyOfAtlas (jointMixedParameterInitializedAtlas B sourceCost rho hrho))) :
    (fun w => passiveOriginalSmallParameter B (passiveOriginalReserveAmplitude sourceCost rho)
      (passiveOriginalReserveAmplitude_pos sourceCost rho hrho) b p₀
      (actualRepairParameterMap
        (tensorChartFamilyOfAtlas (jointMixedParameterInitializedAtlas B sourceCost rho hrho)) b p₀ w)) =ᶠ[𝓝 v]
      (id : X → X) := by
  rw [← jointMixedParameterInitializedAtlas_parameter B sourceCost rho hrho b p₀]
  exact passiveOriginalSmallParameter_original_ball_germ
    (jointMixedParameterInitializedAtlas B sourceCost rho hrho)
    (passiveOriginalReserveAmplitude sourceCost rho)
    (passiveOriginalReserveAmplitude_pos sourceCost rho hrho)
    (jointMixedParameterInitializedAtlas_buffer B sourceCost rho hrho) b p₀ hp₀ v hv

theorem jointMixed_parameter_initialized_original_jets
    (B : BufferedAtlas P Ep) (sourceCost rho : ℝ) (hrho : 0 < rho)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (v : X) (hv : ‖v‖ < actualRepairParameterRadius
      (tensorChartFamilyOfAtlas (jointMixedParameterInitializedAtlas B sourceCost rho hrho))) (j : ℕ) :
    iteratedFDeriv ℝ j (fun w =>
      passiveOriginalSmallParameter B (passiveOriginalReserveAmplitude sourceCost rho)
        (passiveOriginalReserveAmplitude_pos sourceCost rho hrho) b p₀
        (actualRepairParameterMap
          (tensorChartFamilyOfAtlas (jointMixedParameterInitializedAtlas B sourceCost rho hrho)) b p₀ w)) v =
      iteratedFDeriv ℝ j (id : X → X) v :=
  ((jointMixed_parameter_initialized_original_germ B sourceCost rho hrho b p₀ hp₀ v hv).iteratedFDeriv ℝ j).eq_of_nhds

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointMixed_parameter_initialized_profiles
#print axioms GlobalEmbedding.Continuation.jointMixed_parameter_initialized_original_jets
