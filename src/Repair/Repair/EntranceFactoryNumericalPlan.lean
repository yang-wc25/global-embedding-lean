import Repair.EntranceActualPrimaryFactory
import Repair.IncrementFactorySecondaryGeometry
import Repair.EntranceSelectedNumericalParameters
import Repair.IncrementNumericalEllipticity

/-!
# The complete numerical factory plan precedes the reference input

Every quantity in this file depends only on dimensions, the original
allowed-class budget, the prescribed transition/cutoff profiles and the
finite label bound. No manifold, atlas, reference map, local piece or
constructed packet is an argument. These formulas are the literal costs
returned by the actual primary and secondary factories.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

structure RepairEntranceFrameNumbers (m d N : ℕ) where
  inverse : ℕ → ℝ
  inverse_nonneg : ∀ j, 0 ≤ inverse j
  cF : ℝ
  cT : ℝ
  MH : ℝ
  cF_pos : 0 < cF
  cT_pos : 0 < cT
  MH_nonneg : 0 ≤ MH

def repairEntranceFrameNumbers (m d N : ℕ)
    (Forward Inverse : ℕ → ℝ) (hForward : ∀ j, 0 ≤ Forward j) (hInverse : ∀ j, 0 ≤ Inverse j)
    (lower kernel C2 : ℝ) (hLower : 0 < lower) (hKernel : 0 < kernel) (hC2 : 0 ≤ C2) :
    RepairEntranceFrameNumbers m d N :=
  let B := 1+Forward 1
  have hB : 0 < B := by dsimp only [B]; have := hForward 1; linarith
  { inverse := Inverse
    inverse_nonneg := hInverse
    cF := lower/B^2
    cT := (kernel/(B^2*actualIncrementSortedSymmetricConstant m))^2
    MH := actualFirstFrameTransferCost Inverse 1*(actualOriginalMapJetCost (m+1) d N 0*C2)
    cF_pos := div_pos hLower (sq_pos_of_pos hB)
    cT_pos := sq_pos_of_pos (div_pos hKernel
      (mul_pos (sq_pos_of_pos hB) (actualIncrementSortedSymmetricConstant_pos m)))
    MH_nonneg := mul_nonneg (actualFirstFrameTransferCost_nonneg _ hInverse 1)
      (mul_nonneg (actualOriginalMapJetCost_nonneg (m+1) d N 0) hC2) }

def RepairEntranceFrameNumbers.tolerance {m d N : ℕ} (a : RepairEntranceFrameNumbers m d N) : ℝ :=
  repairEntranceGeometryTolerance m d N a.inverse a.cF a.cT a.MH a.cF_pos a.cT_pos

theorem RepairEntranceFrameNumbers.tolerance_pos {m d N : ℕ} (a : RepairEntranceFrameNumbers m d N) :
    0 < a.tolerance :=
  repairEntranceGeometryTolerance_pos m d N a.inverse a.inverse_nonneg a.cF a.cT a.MH
    a.cF_pos a.cT_pos a.MH_nonneg

variable {m d N : ℕ}

def repairEntranceFactoryWeightCap (b : RepairReferenceFactoryBudget m d N) (T : ℝ) (labelBound : ℕ) : ℝ :=
  repairReferenceSignedHierarchy b.cover b.operatorBound T ^ labelBound

theorem repairEntranceFactoryWeightCap_one_le (b : RepairReferenceFactoryBudget m d N)
    (T : ℝ) (hT : 0 < T) (labelBound : ℕ) :
    1 ≤ repairEntranceFactoryWeightCap b T labelBound :=
  one_le_pow₀ (repairReferenceSignedHierarchy_gt_one b.cover b.operatorBound T hT.le).le

def repairEntranceFactorySecondaryForward
    (b : RepairReferenceFactoryBudget m d N) (T B0 Bs : ℝ) (labelBound : ℕ)
    (Parameter Spatial : ℕ → ℝ) :=
  incrementScalarForwardProfile (incrementFactorySignedMb b T B0 Bs labelBound Parameter Spatial)
    (incrementFactorySignedCoordinate b B0 Parameter Spatial)
    (incrementFactorySignedPhaseProfile b T B0 Bs labelBound Parameter Spatial)

def repairEntranceFactorySecondaryInverse
    (b : RepairReferenceFactoryBudget m d N) (T B0 Bs : ℝ) (labelBound : ℕ)
    (Parameter Spatial : ℕ → ℝ) :=
  incrementScalarInverseProfile (incrementFactorySignedMu b T)
    (incrementFactorySignedMb b T B0 Bs labelBound Parameter Spatial)
    (incrementFactorySignedCoordinate b B0 Parameter Spatial)
    (incrementFactorySignedPhaseProfile b T B0 Bs labelBound Parameter Spatial)

def repairEntranceFactoryPrimaryFrame
    (b : RepairReferenceFactoryBudget m d N) (T Bp Bs lower C2 : ℝ) (labelBound : ℕ)
    (Spatial : ℕ → ℝ) (hT : 0 < T) (hBp : 0 ≤ Bp) (hBs : 0 ≤ Bs)
    (hLower : 0 < lower) (hC2 : 0 ≤ C2) (hSpatial : ∀ j, 0 ≤ Spatial j) :
    RepairEntranceFrameNumbers m d N :=
  let cap := repairEntranceFactoryWeightCap b T labelBound
  have hCap := repairEntranceFactoryWeightCap_one_le b T hT labelBound
  have hBound : 0 ≤ cap*b.cover.covectorBound := mul_nonneg (zero_le_one.trans hCap) b.cover.covectorBound_pos.le
  have hMu := (round4UniformTemplateCovectorLower_spec
    (EuclideanSpace ℝ (Fin (m+1))) (EuclideanSpace ℝ (Fin N)) b.templateDim b.operatorBound
    b.phaseMargin b.tensorLower b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos).1
  have hInv := actualPhaseInverseConstant_one_le hMu (show 0 ≤ 2*(cap*b.cover.covectorBound) by positivity)
  repairEntranceFrameNumbers m d N (repairEntranceFactoryNativeForward b cap Bp Bs Spatial)
    (repairEntranceFactoryNativeInverse b cap Bp Bs Spatial)
    (repairEntranceSpatialNativeForward_nonneg (hBp.trans (le_max_left _ _)) (by positivity) hSpatial)
    (repairEntranceSpatialNativeInverse_nonneg (hBp.trans (le_max_left _ _))
      (mul_nonneg (by norm_num) (zero_le_one.trans hInv)) hSpatial)
    lower (b.cover.restrictionReserve/T^2) C2 hLower
    (div_pos b.cover.restrictionReserve_pos (sq_pos_of_pos hT)) hC2

def repairEntranceFactorySecondaryFrame
    (b : RepairReferenceFactoryBudget m d N) (T B0 Bs lower C2 : ℝ) (labelBound : ℕ)
    (Parameter Spatial : ℕ → ℝ) (hT : 0 < T) (hB0 : 0 ≤ B0) (hBs : 0 ≤ Bs)
    (hRadius : 0 ≤ b.modelRadius) (hLower : 0 < lower) (hC2 : 0 ≤ C2)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j) :
    RepairEntranceFrameNumbers m d N :=
  let hMb := (incrementFactorySignedMb_spec b T B0 Bs labelBound hT.le hB0 hBs hRadius
    Parameter Spatial hParameter hSpatial).1
  let hCoordinate := incrementFactorySignedCoordinate_nonneg b B0 hB0 hRadius Parameter Spatial hParameter
  let hPhase := incrementFactorySignedPhaseProfile_nonneg b T B0 Bs labelBound hT.le hB0 hBs hRadius
    Parameter Spatial hParameter hSpatial
  repairEntranceFrameNumbers m d N (repairEntranceFactorySecondaryForward b T B0 Bs labelBound Parameter Spatial)
    (repairEntranceFactorySecondaryInverse b T B0 Bs labelBound Parameter Spatial)
    (incrementScalarForwardProfile_nonneg _ _ _ hMb hCoordinate hPhase)
    (incrementScalarInverseProfile_nonneg _ _ _ _ (incrementFactorySignedMu_pos b T hT) hMb hCoordinate hPhase)
    lower (incrementFactorySignedKernel b T) C2 hLower (incrementFactorySignedKernel_pos b T hT) hC2

def repairEntranceFactoryParameters
    (b : RepairReferenceFactoryBudget m d N) (T B0 Bp Bs lower rho C2 Given0 tolerance : ℝ)
    (labelBound Ds Dp Lprimary : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (Parameter Spatial : ℕ → ℝ) (hT : 0 < T) (hB0 : 0 ≤ B0) (hBp : 0 ≤ Bp) (hBs : 0 ≤ Bs)
    (hRadius : 0 ≤ b.modelRadius) (hLower : 0 < lower) (hrho : 0 < rho) (hC2 : 0 ≤ C2)
    (hTolerance : 0 < tolerance) (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j) :
    RepairEntranceParameters :=
  let primary := repairEntranceFactoryPrimaryFrame b T Bp Bs lower C2 labelBound Spatial hT hBp hBs hLower hC2 hSpatial
  let secondary := repairEntranceFactorySecondaryFrame b T B0 Bs lower C2 labelBound Parameter Spatial
    hT hB0 hBs hRadius hLower hC2 hParameter hSpatial
  let phaseTolerance := min primary.tolerance secondary.tolerance
  let geometryTolerance := min primary.tolerance
    (min secondary.tolerance (incrementOriginalEllipticityTolerance (m+1) d N lower))
  repairEntranceSelectedParameters m d N Ds Dp Lprimary radius hradius primary.cF primary.cT secondary.cT
    lower rho C2 Given0 phaseTolerance geometryTolerance tolerance hrho hC2
    (lt_min primary.tolerance_pos secondary.tolerance_pos)
    (lt_min primary.tolerance_pos (lt_min secondary.tolerance_pos
      (incrementOriginalEllipticityTolerance_pos (m+1) d N lower hLower))) hTolerance

def repairEntranceFactoryProfiles
    (b : RepairReferenceFactoryBudget m d N) (T B0 Bp Bs : ℝ) (labelBound Ds Dp : ℕ)
    (BS TS BP TP Parent Parameter Spatial Given reference envelope : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j) (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j)
    (hReference : ∀ j, 0 ≤ reference j) (hEnvelope : ∀ j, 0 ≤ envelope j) :
    RepairEntranceProfiles :=
  let cap := repairEntranceFactoryWeightCap b T labelBound
  let SF := repairEntranceFactorySecondaryForward b T B0 Bs labelBound Parameter Spatial
  let SI := repairEntranceFactorySecondaryInverse b T B0 Bs labelBound Parameter Spatial
  repairEntranceSelectedProfiles BS TS BP TP
    (repairEntranceFactoryInverse b cap Bp Bs Parameter Spatial)
    (repairEntranceFactoryForward b cap Bp Bs Parameter Spatial)
    Given reference envelope (repairEntranceFactoryMeta b cap Bp Bs Parent Parameter Spatial)
    (incrementSecondaryCutoffProfile (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1)))
      (incrementFactorySignedMu b T) (incrementFactorySignedMb b T B0 Bs labelBound Parameter Spatial)
      (incrementFactorySignedBuffer b Parameter Spatial) BS TS BP TP Ds Dp)
    (repairEntranceOriginalInverseProfile Bp Bs SI Parameter Spatial)
    (repairEntranceOriginalForwardProfile Bp SF Parameter Spatial)
    hBS hTS hBP hTP hReference hEnvelope

theorem repairEntranceFactoryProfiles_reference_prefix
    (b : RepairReferenceFactoryBudget m d N) (T B0 Bp Bs : ℝ) (labelBound Ds Dp J : ℕ)
    (BS TS BP TP Parent Parameter Spatial Given reference envelope Given' reference' envelope' : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j) (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j)
    (hReference : ∀ j, 0 ≤ reference j) (hEnvelope : ∀ j, 0 ≤ envelope j)
    (hReference' : ∀ j, 0 ≤ reference' j) (hEnvelope' : ∀ j, 0 ≤ envelope' j)
    (hGiven : ∀ j, j ≤ J → Given j=Given' j)
    (hRef : ∀ j, j ≤ J → reference j=reference' j)
    (hEnv : ∀ j, j ≤ J → envelope j=envelope' j) :
    (repairEntranceFactoryProfiles b T B0 Bp Bs labelBound Ds Dp BS TS BP TP Parent Parameter Spatial
      Given reference envelope hBS hTS hBP hTP hReference hEnvelope).Prefix
      (repairEntranceFactoryProfiles b T B0 Bp Bs labelBound Ds Dp BS TS BP TP Parent Parameter Spatial
        Given' reference' envelope' hBS hTS hBP hTP hReference' hEnvelope') J :=
  ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,
    hGiven,hRef,hEnv,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntranceFactoryParameters
#print axioms GlobalEmbedding.Continuation.repairEntranceFactoryProfiles_reference_prefix
