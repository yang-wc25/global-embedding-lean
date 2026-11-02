import Repair.IncrementRegionOriginalReserve

/-! Complete actual secondary signed regions: the real geometric buffer,
all four literal phase jets, noncriticality, and the original Sym² kernel
reserve are assembled with one numerical profile and one common margin. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter Metric
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance regionFactoryRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance regionFactorySquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
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
variable {K : Set ((SymmetricSquare (EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
  EuclideanSpace ℝ (Fin N)) × (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
    EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ))}

theorem incrementRegionPhaseProfile_nonneg
    (C : UniformActualGoodDictionaryCover K) (R T coordinateBound sourceBound : ℝ)
    (hT : 0 ≤ T) (hCoordinate : 0 ≤ coordinateBound) (hSource : 0 ≤ sourceBound)
    (labelBound : ℕ) (Spatial : ℕ → ℝ) (hSpatial : ∀ j, 0 ≤ Spatial j) (j : ℕ) :
    0 ≤ incrementRegionPhaseProfile C R T coordinateBound sourceBound labelBound Spatial j := by
  exact mul_nonneg (mul_nonneg (pow_nonneg (zero_lt_one.trans
    (repairReferenceSignedHierarchy_gt_one C R T hT)).le _) C.covectorBound_pos.le)
    (add_nonneg (incrementRegionTransitionProfile_nonneg _ _ _ hCoordinate hSource hSpatial j)
      (incrementRegionTransitionProfile_nonneg _ _ _ hCoordinate hSource hSpatial j))

theorem increment_actual_complete_signed_region
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (C : UniformActualGoodDictionaryCover K) (R T : ℝ) (hT : 0 < T) (labelBound : ℕ)
    (literal : IncrementActualLiteralPhaseData Data C R T labelBound)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (theta : Ep × M → ℝ) (radius buffer coordinateBound sourceBound : ℝ) (hBuffer : 0 < buffer)
    (geometry : RepairReferenceActualInteractionGeometry Data i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M)) theta radius buffer coordinateBound)
    (hSourceBound : ∀ ih y, y ∈ Data.sourceNormDomain ih → ‖y‖ ≤ sourceBound)
    (Parameter Spatial : ℕ → ℝ) (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (hSpatial : Spatial 1 ≤ T) :
    Nonempty (IncrementActualSignedRegion Data i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M)) theta
      ((C.covectorRadius/2)/T) radius buffer coordinateBound (incrementUniformSignedMargin C R/T^2)
      (incrementRegionPhaseProfile C R T coordinateBound sourceBound labelBound Spatial)) := by
  let phase := ((actualOriginalParameterSignedPhase Data i r.val) ∘
    (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm)
  have hJets := increment_actual_region_phase_jets Data hd C R T hT.le labelBound literal
    i r theta radius buffer coordinateBound sourceBound geometry hSourceBound Parameter Spatial transition
  have hReserve := increment_actual_region_original_reserves Data hd hs C R T hT labelBound literal
    i r theta radius buffer coordinateBound geometry Parameter Spatial transition hSpatial
  refine ⟨{ domain := geometry.domain
            center := geometry.center
            isOpen := geometry.isOpen
            carrier_radius := geometry.carrier_radius
            carrier_buffer := geometry.carrier_buffer
            target := geometry.target
            parent := geometry.parent
            active := geometry.active
            inner := geometry.inner
            samples := geometry.samples
            coordinates := geometry.coordinates
            phase_smooth := hJets.1
            phase_noncritical := ?_
            phase_jets := hJets.2
            original_kernel := fun z hz => (hReserve z hz).2 }⟩
  intro z hz
  have hzDomain : z ∈ geometry.domain := geometry.carrier_buffer z hz (mem_ball_self hBuffer)
  have hDiff : DifferentiableAt ℝ phase z :=
    (hJets.1.contDiffAt (geometry.isOpen.mem_nhds hzDomain)).differentiableAt (by simp)
  have he : fderiv ℝ (fun x : D => actualOriginalParameterSignedPhase Data i r.val
      (z.1,(Data.atlas.chart i.1).symm x)) z.2 =
      (fderiv ℝ phase z).comp (ContinuousLinearMap.inr ℝ Ep D) :=
    by
      have hi : HasFDerivAt (fun x : D => (z.1,x)) (ContinuousLinearMap.inr ℝ Ep D) z.2 :=
        hasFDerivAt_prodMk_right z.1 z.2
      have hg : HasFDerivAt phase (fderiv ℝ phase z) (z.1,z.2) := hDiff.hasFDerivAt
      exact (hg.comp z.2 hi).fderiv
  rw [← he]
  exact (hReserve z hzDomain).1

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementRegionPhaseProfile_nonneg
#print axioms GlobalEmbedding.Continuation.increment_actual_complete_signed_region
