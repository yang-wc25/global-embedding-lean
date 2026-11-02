import FaithfulIncrements.LocalPrimaryFiniteness
import FaithfulIncrements.OriginalPhaseDerivativeIdentity
import Smoothing.ParameterSpatialPackets

/-!
# Same original total and spatial phase covectors have finite norms

The actual scalar phase jets are manufactured from its compact physical
carrier and the original transition bounds. Fixed derivative extractions
then bound the total and spatial covectors. The latter uses the genuine
manifold chain rule for the same phase, not a substituted template phase.
Every original parameter derivative and original Omega/Q sample is kept.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulIncrements

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Y" => Fin (n+d) → ℝ

theorem local_primary_phase_derivative_weighted_finite
    {a : ℕ} (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (nu : Fin Data.primaryCount) (hOpen : IsOpen (domain nu))
    (hCompact : IsCompact (closure (domain nu)))
    (hClosure : closure (domain nu) ⊆
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (hTransition : ∀ i l k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample Data (i,l),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition Data i l) y‖ ≤ T k)
    (L : (Y →L[ℝ] ℝ) →L[ℝ] (Fin a → ℝ))
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell
      (fun i => L ∘ fderiv ℝ (actualOriginalJointPhase Data nu i))
      (incrementsOriginalPrimaryDifferentiation (localPrimaryData Data V domain) nu)
      (incrementsOriginalPrimaryEvaluation (localPrimaryData Data V domain) nu) ≠ ⊤ := by
  let D := localPrimaryData Data V domain
  let O := incrementsOriginalPrimaryDifferentiation D nu
  let S := incrementsOriginalPrimaryEvaluation D nu
  have hO : ∀ i, IsOpen (O i) := fun i =>
    (actual_original_jointPoint_continuousOn Data i).isOpen_inter_preimage
      (parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart i) hOpen
  have hSO : ∀ i, S i ⊆ O i := fun i y hy => ⟨hy.1.1,hy.2⟩
  have hOld : ∀ i, O i ⊆ actualOriginalPhaseOpen Data nu i := by
    intro i y hy
    have h := hClosure (subset_closure hy.2)
    exact ⟨⟨hy.1,h.1⟩,hy.1,h.2⟩
  have hf : ∀ i, ContDiffOn ℝ ∞ (actualOriginalJointPhase Data nu i) (O i) :=
    fun i => (actualOriginalJointPhase_contDiffOn Data hd hs nu i).mono (hOld i)
  have hdf : ∀ i, ContDiffOn ℝ ∞
      (L ∘ fderiv ℝ (actualOriginalJointPhase Data nu i)) (O i) := fun i =>
    L.contDiff.comp_contDiffOn ((hf i).fderiv_of_isOpen (hO i) (m := ∞) (by simp))
  obtain ⟨B,hB,hJets⟩ := local_primary_phase_jet_profile Data hd hs V domain nu
    hCompact hClosure T hT hTransition
  apply paperAtlasWeighted_ne_top base j ell _ O S hO hSO hdf
  intro i k _
  refine ⟨‖L‖*B (k+1),?_⟩
  rintro _ ⟨y,rfl⟩
  exact increment_given_derivative_extraction_jets L (actualOriginalJointPhase Data nu i)
    y ((hf i).contDiffAt ((hO i).mem_nhds (hSO i y.property))) k _
    (hJets i (k+1) y y.property)

theorem local_primary_total_phase_weighted_finite
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (nu : Fin Data.primaryCount) (hOpen : IsOpen (domain nu))
    (hCompact : IsCompact (closure (domain nu)))
    (hClosure : closure (domain nu) ⊆
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (hTransition : ∀ i l k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample Data (i,l),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition Data i l) y‖ ≤ T k)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell
      (actualOriginalTotalPhaseCoordinates (localPrimaryData Data V domain) nu)
      (incrementsOriginalPrimaryDifferentiation (localPrimaryData Data V domain) nu)
      (incrementsOriginalPrimaryEvaluation (localPrimaryData Data V domain) nu) ≠ ⊤ :=
  local_primary_phase_derivative_weighted_finite Data hd hs V domain nu
    hOpen hCompact hClosure T hT hTransition (incrementGivenTotalExtraction (n+d)) base j ell

theorem local_primary_spatial_phase_weighted_finite
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (nu : Fin Data.primaryCount) (hOpen : IsOpen (domain nu))
    (hCompact : IsCompact (closure (domain nu)))
    (hClosure : closure (domain nu) ⊆
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (hTransition : ∀ i l k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample Data (i,l),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition Data i l) y‖ ≤ T k)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell
      (incrementsOriginalPhaseCovectorCoordinates (localPrimaryData Data V domain) nu)
      (incrementsOriginalPrimaryDifferentiation (localPrimaryData Data V domain) nu)
      (incrementsOriginalPrimaryEvaluation (localPrimaryData Data V domain) nu) ≠ ⊤ := by
  have hFinite := local_primary_phase_derivative_weighted_finite Data hd hs V domain nu
    hOpen hCompact hClosure T hT hTransition (incrementGivenSpatialExtraction n d) base j ell
  let D := localPrimaryData Data V domain
  let O := incrementsOriginalPrimaryDifferentiation D nu
  let S := incrementsOriginalPrimaryEvaluation D nu
  have hSO : ∀ i, S i ⊆ O i := fun i y hy => ⟨hy.1.1,hy.2⟩
  have hEq : ∀ i, EqOn (incrementsOriginalPhaseCovectorCoordinates D nu i)
      ((incrementGivenSpatialExtraction n d) ∘ fderiv ℝ (actualOriginalJointPhase Data nu i)) (O i) := by
    intro i y hy
    have h := hClosure (subset_closure hy.2)
    exact original_phase_spatial_coordinates Data hd hs nu i y ⟨⟨hy.1,h.1⟩,h.2⟩
  rw [paperAtlasWeighted_congr_on base j ell O S hSO hEq]
  exact hFinite

end GlobalEmbedding.Continuation.FaithfulIncrements
#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.local_primary_total_phase_weighted_finite
#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.local_primary_spatial_phase_weighted_finite

