import NormalPolar.ActualProbeInitialSupplyAssembly
import NormalPolar.ActualRepairModelFirstDefectStateEntrance

/-! The actual contracted first target and its fixed original input profile.
It is constructed from the reference metric in the immutable smoothing
packet. One profile, computed at scale one, bounds every smaller scale and
every admitted first-step contraction. It is original input data, independent
of the eventual primary, secondary, first state or repair trajectory. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Topology Classical
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,Es)
variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference Given : ℕ → ℝ}

def actualProbeInitialReferenceGerm
    (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
    (hmetric : packet.metric = Data.H) :
    parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ :=
  ⟨Data.H,⟨by
    intro i
    refine ⟨incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i,
      parameterRound2_originalDifferentiation_open _ _ i,fun _ hy => hy.1,?_⟩
    rw [← hmetric]
    exact packet.metric_smooth i,
    by intro z hz; rw [← hmetric]; exact packet.metric_symmetric z.1 z.2⟩⟩

def actualProbeInitialReferenceProfile
    (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
    (hmetric : packet.metric = Data.H) (j : ℕ) : ℝ :=
  parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples
    univ packet.closedSamples_compact (fun _ _ hy => hy.1) 1 j (actualProbeInitialReferenceGerm packet hmetric)

def actualProbeInitialTargetGerm
    (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
    (hmetric : packet.metric = Data.H) (t : ℝ) :
    parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ :=
  (1-((t^((6 : ℝ)/5))^10/(t^10))^2) • actualProbeInitialReferenceGerm packet hmetric

theorem actualProbeInitialSupply_reference_scaled_profile
    (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
    (hmetric : packet.metric = Data.H) (scalar ell : ℝ) (hscalar : 0 ≤ scalar) (hscalar1 : scalar ≤ 1)
    (hell1 : ell ≤ 1) (j : ℕ) :
    parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples
      univ packet.closedSamples_compact (fun _ _ hy => hy.1) ell j
      (scalar • actualProbeInitialReferenceGerm packet hmetric) ≤ actualProbeInitialReferenceProfile packet hmetric j := by
  let G := actualProbeInitialReferenceGerm packet hmetric
  have hmono : parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples
      univ packet.closedSamples_compact (fun _ _ hy => hy.1) ell j G ≤
      actualProbeInitialReferenceProfile packet hmetric j :=
    ENNReal.toReal_mono
      (parameterRound2_tensorGerm_weighted_finite Data.atlas packet.parameterFamily.chart packet.closedSamples
        univ packet.closedSamples_compact (fun _ _ hy => hy.1) G 0 j 1)
      (parameterRound2_paperAtlasWeighted_mono_scale 0 j ell 1 hell1
        (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart G.val)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples)
  rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg hscalar]
  exact (mul_le_mul_of_nonneg_left hmono hscalar).trans
    (mul_le_of_le_one_left (apply_nonneg _ _) hscalar1)

theorem actualProbeInitialSupply_target_original_profile
    (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
    (hmetric : packet.metric = Data.H) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    (actualProbeInitialTargetGerm packet hmetric t).val =
      (fun p x => (1-((t^((6 : ℝ)/5))^10/(t^10))^2) •
        inducedMetric (I := IM) (fun y => packet.referenceMap (p,y)) x) ∧
    ∀ ell : ℝ, ell ≤ 1 → ∀ j,
      parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples
        univ packet.closedSamples_compact (fun _ _ hy => hy.1) ell j
        (actualProbeInitialTargetGerm packet hmetric t) ≤ actualProbeInitialReferenceProfile packet hmetric j := by
  have htau : 0 < t^((6 : ℝ)/5) := Real.rpow_pos_of_pos ht _
  have htauT : t^((6 : ℝ)/5) ≤ t := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num : (1 : ℝ) ≤ 6/5)
  have hratio : 0 ≤ (t^((6 : ℝ)/5))^10/(t^10) := div_nonneg (pow_nonneg htau.le _) (pow_nonneg ht.le _)
  have hratio1 : (t^((6 : ℝ)/5))^10/(t^10) ≤ 1 :=
    (div_le_one (pow_pos ht _)).2 (pow_le_pow_left₀ htau.le htauT _)
  have hs : 0 ≤ 1-((t^((6 : ℝ)/5))^10/(t^10))^2 := by nlinarith
  have hs1 : 1-((t^((6 : ℝ)/5))^10/(t^10))^2 ≤ 1 := sub_le_self _ (sq_nonneg _)
  constructor
  · change (1-((t^((6 : ℝ)/5))^10/(t^10))^2) • Data.H = _
    rw [packet.reference_tensor]
    rfl
  · intro ell hell1 j
    exact actualProbeInitialSupply_reference_scaled_profile packet hmetric _ ell hs hs1 hell1 j

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialReferenceGerm
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_reference_scaled_profile
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_target_original_profile
