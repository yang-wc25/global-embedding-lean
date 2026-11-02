import NormalPolar.OriginalWaveSeedParameterBall

/-! Non-circular parameter initialization. A primitive source cost is fixed
first. Its reserve amplitude then selects a legal common buffer, leaving
the actual charts, inner domains, supports and original norm samples fixed.
The future original repair ball is defined only after this initialization.
The small global parameter itself is unchanged by the idempotent choice. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {d : ℕ} {P : Type*} [TopologicalSpace P]

theorem jointMixed_parameter_amplitude_atlas_idempotent
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (amplitude : ℝ) (ha : 0 < amplitude) :
    passiveOriginalAmplitudeAtlas (passiveOriginalAmplitudeAtlas B amplitude ha) amplitude ha =
      passiveOriginalAmplitudeAtlas B amplitude ha := by
  cases B
  simp only [passiveOriginalAmplitudeAtlas,passiveOriginalSmallBuffer,min_assoc,min_self]

theorem jointMixed_parameter_amplitude_chartfamily_idempotent
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (amplitude : ℝ) (ha : 0 < amplitude) :
    (tensorChartFamilyOfAtlas
      (passiveOriginalAmplitudeAtlas (passiveOriginalAmplitudeAtlas B amplitude ha) amplitude ha) :
        TensorBufferedChartFamily (Fin B.count) P (EuclideanSpace ℝ (Fin d))) =
      tensorChartFamilyOfAtlas (passiveOriginalAmplitudeAtlas B amplitude ha) := by
  cases B
  simp only [tensorChartFamilyOfAtlas,passiveOriginalAmplitudeAtlas,passiveOriginalSmallBuffer,
    min_assoc,min_self]

def jointMixedParameterInitializedAtlas
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (sourceCost rho : ℝ) (hrho : 0 < rho) :
    BufferedAtlas P (EuclideanSpace ℝ (Fin d)) :=
  passiveOriginalAmplitudeAtlas B (passiveOriginalReserveAmplitude sourceCost rho)
    (passiveOriginalReserveAmplitude_pos sourceCost rho hrho)

theorem jointMixedParameterInitializedAtlas_buffer
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (sourceCost rho : ℝ) (hrho : 0 < rho) :
    (jointMixedParameterInitializedAtlas B sourceCost rho hrho).buffer ≤
      passiveOriginalReserveAmplitude sourceCost rho /
        (‖(EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap‖+1) :=
  min_le_right _ _

theorem jointMixedParameterInitializedAtlas_chart
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (sourceCost rho : ℝ) (hrho : 0 < rho) :
    (jointMixedParameterInitializedAtlas B sourceCost rho hrho).chart = B.chart := rfl

theorem jointMixedParameterInitializedAtlas_inner_support
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (sourceCost rho : ℝ) (hrho : 0 < rho) :
    (jointMixedParameterInitializedAtlas B sourceCost rho hrho).inner = B.inner ∧
      (jointMixedParameterInitializedAtlas B sourceCost rho hrho).support = B.support := ⟨rfl,rfl⟩

variable [T2Space P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem jointMixedParameterInitializedAtlas_smooth
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hB : IsSmoothBufferedAtlas B)
    (sourceCost rho : ℝ) (hrho : 0 < rho) :
    IsSmoothBufferedAtlas (jointMixedParameterInitializedAtlas B sourceCost rho hrho) :=
  ⟨hB.chart_mem,hB.support_subset⟩

theorem jointMixedParameterInitializedAtlas_parameter
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (sourceCost rho : ℝ) (hrho : 0 < rho)
    (b : Fin B.count) (p₀ : P) :
    passiveOriginalSmallParameter (jointMixedParameterInitializedAtlas B sourceCost rho hrho)
      (passiveOriginalReserveAmplitude sourceCost rho)
      (passiveOriginalReserveAmplitude_pos sourceCost rho hrho) b p₀ =
    passiveOriginalSmallParameter B (passiveOriginalReserveAmplitude sourceCost rho)
      (passiveOriginalReserveAmplitude_pos sourceCost rho hrho) b p₀ := by
  unfold jointMixedParameterInitializedAtlas passiveOriginalSmallParameter
  exact congrArg (fun C : TensorBufferedChartFamily (Fin B.count) P (EuclideanSpace ℝ (Fin d)) =>
    actualRepairGlobalParameter C b p₀)
    (jointMixed_parameter_amplitude_chartfamily_idempotent B
      (passiveOriginalReserveAmplitude sourceCost rho)
      (passiveOriginalReserveAmplitude_pos sourceCost rho hrho))

theorem jointMixedParameterInitializedAtlas_samples
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (sourceCost rho : ℝ) (hrho : 0 < rho)
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (hQ : ∀ i, IsCompact (Q i) ∧ Q i ⊆ (B.chart i).target ∧
      closure (bufferedSamplingCoordinates B i) ⊆ Q i) :
    ∀ i, IsCompact (Q i) ∧
      Q i ⊆ ((jointMixedParameterInitializedAtlas B sourceCost rho hrho).chart i).target ∧
      closure (bufferedSamplingCoordinates (jointMixedParameterInitializedAtlas B sourceCost rho hrho) i) ⊆ Q i :=
  passiveOriginalSmallBuffer_samples B _
    (div_pos (passiveOriginalReserveAmplitude_pos sourceCost rho hrho)
      (by positivity)) Q hQ

variable {n N : ℕ} {M S : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [Subsingleton S]

theorem jointMixedParameterInitializedAtlas_data
    (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (sourceCost rho : ℝ) (hrho : 0 < rho)
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d))) :
    passiveOriginalData s₀ seed (jointMixedParameterInitializedAtlas B sourceCost rho hrho) Q =
      passiveOriginalData s₀ seed B Q := rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointMixed_parameter_amplitude_atlas_idempotent
#print axioms GlobalEmbedding.Continuation.jointMixedParameterInitializedAtlas_parameter
#print axioms GlobalEmbedding.Continuation.jointMixedParameterInitializedAtlas_data
