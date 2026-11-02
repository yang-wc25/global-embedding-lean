import Repair.EntranceUniformReferenceProfiles
import Repair.IncrementUniformSecondaryPacket

/-!
# Original data produces the common low budgets of the same secondary packet

The input certificates contain only the actual native chart functions,
all-order derivatives, and original evaluation samples.  Original map C2
and ellipticity produce the first/Hessian budgets.  The previously proved
uniform transverse reserve is retained.  Every native chart, slice,
cutoff, carrier, partition and local multiplicity is unchanged.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal BigOperators
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

structure IncrementSecondaryNativeChartInputs
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Ref hd hs i r W)
    (Forward Inverse : ℕ → ℝ) : Prop where
  forward : ∀ j z, z ∈ piece.native.source → ‖iteratedFDeriv ℝ j piece.native z‖ ≤ Forward j
  inverse : ∀ j z, z ∈ piece.native.target → ‖iteratedFDeriv ℝ j piece.native.symm z‖ ≤ Inverse j
  source_samples : ∀ z, z ∈ piece.native.source →
    parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet i

def incrementNumericalSecondaryReferencePiece
    (Forward Inverse : ℕ → ℝ) (hForward : ∀ j, 0 ≤ Forward j) (hInverse : ∀ j, 0 ≤ Inverse j)
    (lower C2 : ℝ) (hLower : 0 < lower) (hC2 : 0 ≤ C2)
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hAll : Ref.parameterSet = univ)
    (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ Ref.F)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (hMapFinite : paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet) ≠ ⊤)
    (hMap : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet)).toReal ≤ C2)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Ref hd hs i r W)
    (chart : IncrementSecondaryNativeChartInputs Ref hd hs i r W piece Forward Inverse) :
    Round3PreparedSignedReferencePiece Ref hd hs i r W := by
  let B := 1+Forward 1
  have hB : 0 < B := by dsimp only [B]; have := hForward 1; linarith
  let K := actualOriginalMapJetCost (m+1) d N 0*C2
  have hK : 0 ≤ K := mul_nonneg (actualOriginalMapJetCost_nonneg (m+1) d N 0) hC2
  let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
    Ref.parameterNormDomain Ref.parameterSet
  have hSO : ∀ j, S j ⊆ incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart j :=
    fun _ _ hy => hy.1
  have hCoords := parameterRound2_originalMapCoordinates_contDiffOn Ref.atlas Ref.parameterChart
    hd.atlas_smooth hd.parameter_charts_smooth Ref.F (by simpa only [modelWithCornersSelf_prod] using hFjoint)
  let Fn := fun p x => Ref.F ((Ref.parameterChart i.2).symm p,x)
  have hJoint : ContDiffOn ℝ ∞ (fun z : X => Fn z.1 ((Ref.atlas.chart i.1).symm z.2)) piece.native.source :=
    round4_original_native_host_joint_smooth Ref.atlas Ref.parameterChart Ref.F S hSO hCoords
      i piece.native.source chart.source_samples
  have hNativeForward (y : X) (hy : y ∈ piece.native.source) : ‖fderiv ℝ piece.native y‖ ≤ B := by
    have h := chart.forward 1 y hy
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans (by dsimp only [B]; linarith)
  have hLow := repairEntrance_native_original_low_budgets Fn
    (Ref.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1)
    piece.native _ piece.slices piece.data piece.native.source piece.native.open_source hJoint
    subset_rfl lower B K hLower hB hK Inverse hInverse (by
      intro z hz v
      have hSample := (actual_original_native_evaluation_iff Ref hd i z).mp (chart.source_samples z hz)
      exact hEll.lower ((Ref.parameterChart i.2).symm z.1) hSample.2.2 i.1 z.2 hSample.1 v) (by
      intro k hk z hz
      exact round3_original_C2_native_jets Ref.atlas Ref.parameterChart Ref.F S hSO hCoords
        hMapFinite C2 hMap i k hk z (chart.source_samples z hz)) hNativeForward chart.inverse
  have hSlice (z : X) : actualOriginalOpenParameterSlice Ref i z.1 = Fn z.1 :=
    actualOriginalOpenParameterSlice_eq Ref i z.1
      (hd.parameter_subset (by rw [hAll]; exact mem_univ _))
  exact { piece with
    cF := lower/B^2
    cF_pos := div_pos hLower (sq_pos_of_pos hB)
    MH := actualFirstFrameTransferCost Inverse 1*K
    MH_nonneg := mul_nonneg (actualFirstFrameTransferCost_nonneg _ hInverse 1) hK
    Bnative := B
    Bnative_pos := hB
    native_first := hNativeForward
    first := by
      intro z hz v
      rw [hSlice]
      exact hLow.1 z hz v
    hessian := by
      intro z hz
      rw [hSlice]
      exact hLow.2 z hz
    Tinv := Inverse
    Tinv_nonneg := hInverse
    inverse_jets := chart.inverse
    Forward := Forward
    Forward_nonneg := hForward
    forward_jets := chart.forward }

def incrementNumericalSecondaryPacket
    (Forward Inverse : ℕ → ℝ) (hForward : ∀ j, 0 ≤ Forward j) (hInverse : ∀ j, 0 ≤ Inverse j)
    (lower C2 : ℝ) (hLower : 0 < lower) (hC2 : 0 ≤ C2)
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hAll : Ref.parameterSet = univ)
    (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ Ref.F)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (hMapFinite : paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet) ≠ ⊤)
    (hMap : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet)).toReal ≤ C2)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (old : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
    (chart : ∀ r i a, IncrementSecondaryNativeChartInputs Ref hd hs i r _
      (old.piece r i a) Forward Inverse) :
    Round3PreparedParameterSecondaryPacket Ref hd hs theta where
  s := old.s
  piece := fun r i a => incrementNumericalSecondaryReferencePiece Forward Inverse hForward hInverse
    lower C2 hLower hC2 Ref hd hs hAll hFjoint hEll hMapFinite hMap i r _ (old.piece r i a) (chart r i a)
  native_parent := old.native_parent
  smooth := old.smooth
  compact := old.compact
  parent := old.parent
  source := old.source
  partition := old.partition
  count := old.count

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementNumericalSecondaryReferencePiece
#print axioms GlobalEmbedding.Continuation.incrementNumericalSecondaryPacket
