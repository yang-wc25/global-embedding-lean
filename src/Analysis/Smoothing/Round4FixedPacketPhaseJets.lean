import Probes.ActualOriginalPhaseProfileJets
import Smoothing.ParameterRound2OriginalFixedPacket

/-! The actual phase jets use only the unchanged fixed packet. Neither the
current map nor its tensor nor the full input max is needed for this producer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff ENNReal Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "X" => Ep × Es

private local instance phaseProfileProductCharted : ChartedSpace X (P × M) :=
  prodChartedSpace Ep P Es M
private local instance phaseProfileProductManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

theorem round4_actual_fixed_packet_phase_positive_jets
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (hs : IncrementsOriginalSmoothInputs D) (j : ℕ) (ell budget : ℝ) (hell : 0 < ell)
    (hfinite : parameterRound2_originalFixedPacketProfile D j ell ≠ ⊤)
    (hbudget : (parameterRound2_originalFixedPacketProfile D j ell).toReal ≤ budget)
    (nu : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount)
    (k : ℕ) (hk : k ≤ j) (z : X)
    (hz : parameterTensorModelEquiv n d z ∈ incrementsOriginalPrimaryEvaluation D nu i) :
    ell^k*‖iteratedFDeriv ℝ (k+1)
      (actualOriginalJointPhase D nu i ∘ parameterTensorModelEquiv n d) z‖ ≤
        actualOriginalTotalPhaseJetCost n d j*budget := by
  let O := incrementsOriginalPrimaryDifferentiation D nu
  let U := actualOriginalPhaseOpen D nu
  let S := incrementsOriginalPrimaryEvaluation D nu
  let f := actualOriginalTotalPhaseCoordinates D nu
  let a := parameterTensorModelEquiv n d
  have hO (i) := actual_original_primaryDifferentiation_open D hd.primary_open nu i
  have hU (i) := actualOriginalPhaseOpen_open D hd nu i
  have hSU (i) := actualOriginalPhaseOpen_sample D hd nu i
  have hf (i) := actualOriginalTotalPhaseCoordinates_contDiffOn D hd hs nu i
  have hle : paperAtlasWeighted 0 j ell f O S ≤
      parameterRound2_originalFixedPacketProfile D j ell := by
    unfold parameterRound2_originalFixedPacketProfile
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply le_max_of_le_left
    exact le_iSup (fun ν : Fin D.primaryCount => paperAtlasWeighted 0 j ell
      (actualOriginalTotalPhaseCoordinates D ν) (incrementsOriginalPrimaryDifferentiation D ν)
        (incrementsOriginalPrimaryEvaluation D ν)) nu
  have hfin : paperAtlasWeighted 0 j ell f O S ≠ ⊤ := ne_top_of_le_ne_top hfinite hle
  have hbound : (paperAtlasWeighted 0 j ell f O S).toReal ≤ budget :=
    (ENNReal.toReal_mono hfinite hle).trans hbudget
  have he := actual_paperAtlasWeighted_open_restrict 0 j ell f O U S hO hU
    (fun _ => inter_subset_left) hSU
  rw [he] at hfin hbound
  have hj := paperAtlasWeighted_shifted_joint_jet_le 0 j ell hell f U S hU hSU hf hfin i hk
    (le_refl 0) hz
  simp only [Nat.add_zero] at hj
  have hcoef : ell^k*‖iteratedFDeriv ℝ k (f i) (a z)‖ ≤ coordinateDimensionFactor (n+d) j*budget :=
    hj.trans (mul_le_mul_of_nonneg_left hbound (coordinateDimensionFactor_nonneg _ _))
  have hDf : fderiv ℝ (actualOriginalJointPhase D nu i) = actualScalarCovectorAssembly (n+d) ∘ f i := by
    funext y
    exact (actualScalarCovectorAssembly_exact (n+d) (fderiv ℝ (actualOriginalJointPhase D nu i) y)).symm
  have hp := slow_linear_jet_bound (actualScalarCovectorAssembly (n+d)) (U i) (hU i) (f i) (hf i)
    k ell (coordinateDimensionFactor (n+d) j*budget) hell.le (a z) (hSU i hz) hcoef
  rw [← hDf,norm_iteratedFDeriv_fderiv] at hp
  have hpre := norm_iteratedFDeriv_comp_equiv_le a (actualOriginalJointPhase D nu i) (k+1) z
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hbudget
  calc
    _ ≤ ell^k*(‖iteratedFDeriv ℝ (k+1) (actualOriginalJointPhase D nu i) (a z)‖*
        linearModelFactor a (k+1)) := mul_le_mul_of_nonneg_left hpre (pow_nonneg hell.le k)
    _ = linearModelFactor a (k+1)*(ell^k*‖iteratedFDeriv ℝ (k+1) (actualOriginalJointPhase D nu i) (a z)‖) := by ring
    _ ≤ linearModelFactor a (j+1)*(‖actualScalarCovectorAssembly (n+d)‖*
        (coordinateDimensionFactor (n+d) j*budget)) :=
      mul_le_mul (linearModelFactor_mono a (by omega)) hp (by positivity) (linearModelFactor_nonneg _ _)
    _ = _ := by dsimp only [actualOriginalTotalPhaseJetCost,a]; ring

#print axioms round4_actual_fixed_packet_phase_positive_jets
end GlobalEmbedding.Continuation
