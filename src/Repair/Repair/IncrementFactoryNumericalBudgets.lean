import Repair.IncrementFactoryLiteralData
import Repair.ReferenceOriginalLocalFactoryInteraction

/-! Numerical budgets for the actual factory's nonlinear secondary
charts. Each is a function of the common reference class and original
transition profiles, before selecting any seed or secondary piece. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ}

def incrementFactoryJointProfile (Parameter Spatial : ℕ → ℝ) (j : ℕ) : ℝ :=
  max (Parameter j) (Spatial j)

def incrementFactorySignedBuffer (b : RepairReferenceFactoryBudget m d N)
    (Parameter Spatial : ℕ → ℝ) : ℝ :=
  repairReferenceFactoryInteractionBuffer b (incrementFactoryJointProfile Parameter Spatial)

def incrementFactorySignedCoordinate (b : RepairReferenceFactoryBudget m d N)
    (B0 : ℝ) (Parameter Spatial : ℕ → ℝ) : ℝ :=
  B0+b.modelRadius+incrementFactorySignedBuffer b Parameter Spatial

def incrementFactorySignedMu (b : RepairReferenceFactoryBudget m d N) (T : ℝ) : ℝ :=
  (b.cover.covectorRadius/2)/T

def incrementFactorySignedKernel (b : RepairReferenceFactoryBudget m d N) (T : ℝ) : ℝ :=
  incrementUniformSignedMargin b.cover b.operatorBound/T^2

def incrementFactorySignedPhaseProfile (b : RepairReferenceFactoryBudget m d N)
    (T B0 Bs : ℝ) (labelBound : ℕ) (Parameter Spatial : ℕ → ℝ) : ℕ → ℝ :=
  incrementRegionPhaseProfile b.cover b.operatorBound T
    (incrementFactorySignedCoordinate b B0 Parameter Spatial) Bs labelBound Spatial

def incrementFactorySignedMb (b : RepairReferenceFactoryBudget m d N)
    (T B0 Bs : ℝ) (labelBound : ℕ) (Parameter Spatial : ℕ → ℝ) : ℝ :=
  incrementFactorySignedPhaseProfile b T B0 Bs labelBound Parameter Spatial 1 +
    incrementFactorySignedBuffer b Parameter Spatial *
      incrementFactorySignedPhaseProfile b T B0 Bs labelBound Parameter Spatial 2

theorem incrementFactorySignedBuffer_pos (b : RepairReferenceFactoryBudget m d N)
    (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ j, 0 ≤ Parameter j) :
    0 < incrementFactorySignedBuffer b Parameter Spatial :=
  repairReferenceFactoryInteractionBuffer_pos b _ (fun j => (hParameter j).trans (le_max_left _ _))

theorem incrementFactorySignedMu_pos (b : RepairReferenceFactoryBudget m d N) (T : ℝ) (hT : 0 < T) :
    0 < incrementFactorySignedMu b T := div_pos (div_pos b.cover.covectorRadius_pos (by norm_num)) hT

theorem incrementFactorySignedKernel_pos (b : RepairReferenceFactoryBudget m d N) (T : ℝ) (hT : 0 < T) :
    0 < incrementFactorySignedKernel b T :=
  div_pos (incrementUniformSignedMargin_pos b.cover b.operatorBound) (sq_pos_of_pos hT)

theorem incrementFactorySignedCoordinate_nonneg (b : RepairReferenceFactoryBudget m d N)
    (B0 : ℝ) (hB0 : 0 ≤ B0) (hRadius : 0 ≤ b.modelRadius)
    (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ j, 0 ≤ Parameter j) :
    0 ≤ incrementFactorySignedCoordinate b B0 Parameter Spatial :=
  add_nonneg (add_nonneg hB0 hRadius) (incrementFactorySignedBuffer_pos b Parameter Spatial hParameter).le

theorem incrementFactorySignedPhaseProfile_nonneg (b : RepairReferenceFactoryBudget m d N)
    (T B0 Bs : ℝ) (labelBound : ℕ) (hT : 0 ≤ T) (hB0 : 0 ≤ B0) (hBs : 0 ≤ Bs)
    (hRadius : 0 ≤ b.modelRadius) (Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j) (j : ℕ) :
    0 ≤ incrementFactorySignedPhaseProfile b T B0 Bs labelBound Parameter Spatial j :=
  incrementRegionPhaseProfile_nonneg b.cover b.operatorBound T _ Bs hT
    (incrementFactorySignedCoordinate_nonneg b B0 hB0 hRadius Parameter Spatial hParameter)
    hBs labelBound Spatial hSpatial j

theorem incrementFactorySignedMb_spec (b : RepairReferenceFactoryBudget m d N)
    (T B0 Bs : ℝ) (labelBound : ℕ) (hT : 0 ≤ T) (hB0 : 0 ≤ B0) (hBs : 0 ≤ Bs)
    (hRadius : 0 ≤ b.modelRadius) (Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j) :
    0 ≤ incrementFactorySignedMb b T B0 Bs labelBound Parameter Spatial ∧
    incrementFactorySignedPhaseProfile b T B0 Bs labelBound Parameter Spatial 1 ≤
      incrementFactorySignedMb b T B0 Bs labelBound Parameter Spatial ∧
    incrementFactorySignedBuffer b Parameter Spatial *
      incrementFactorySignedPhaseProfile b T B0 Bs labelBound Parameter Spatial 2 ≤
      incrementFactorySignedMb b T B0 Bs labelBound Parameter Spatial := by
  have h1 := incrementFactorySignedPhaseProfile_nonneg b T B0 Bs labelBound hT hB0 hBs hRadius
    Parameter Spatial hParameter hSpatial 1
  have h2 := mul_nonneg (incrementFactorySignedBuffer_pos b Parameter Spatial hParameter).le
    (incrementFactorySignedPhaseProfile_nonneg b T B0 Bs labelBound hT hB0 hBs hRadius
      Parameter Spatial hParameter hSpatial 2)
  exact ⟨add_nonneg h1 h2,le_add_of_nonneg_right h2,le_add_of_nonneg_left h1⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementFactorySignedMb_spec
