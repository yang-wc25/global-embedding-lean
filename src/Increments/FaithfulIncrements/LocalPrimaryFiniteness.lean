import FaithfulIncrements.LocalPrimaryNeighborhoods
import FaithfulRepair.OriginalMapFiniteness
import Probes.ActualIncrementOriginalCoreFields
import Probes.ActualOriginalPhaseProfileJets

/-!
# Actual primary-field finiteness on unchanged coordinate observations

The manufactured solver neighborhood has compact closure inside the old
smooth domain. Its intersection with the same compact parameter sample is
a compact physical carrier. Actual coordinate transitions propagate jets
from internally manufactured compact chart cores to every point of the
unchanged Omega/Q observations. No compactness of Omega or Q, nor any
high-order numerical input budget, is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulIncrements
open FaithfulRepair

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- Same physical field, actual full coordinate jets, and no substituted
sample domain. This helper applies equally to scalar phases and normals. -/
theorem local_primary_joint_jet_profile
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (nu : Fin Data.primaryCount)
    (hCompact : IsCompact (closure (domain nu)))
    (hClosure : closure (domain nu) ⊆
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (hTransition : ∀ i l k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample Data (i,l),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition Data i l) y‖ ≤ T k)
    (f : P × M → Y)
    (hf : ∀ i, ContDiffOn ℝ ∞
      (f ∘ incrementsOriginalJointPoint Data.atlas Data.parameterChart i)
      (actualOriginalPrimaryCoordinateOpen Data nu i)) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ i k y, y ∈ incrementsOriginalPrimaryEvaluation (localPrimaryData Data V domain) nu i →
        ‖iteratedFDeriv ℝ k
          (f ∘ incrementsOriginalJointPoint Data.atlas Data.parameterChart i) y‖ ≤ C k := by
  let chart := originalJointCoordinateChart Data
  let C := closure (domain nu) ∩ (Data.parameterSet ×ˢ (univ : Set M))
  let W := Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data
  let S := incrementsOriginalPrimaryEvaluation (localPrimaryData Data V domain) nu
  have hC : IsCompact C :=
    hCompact.inter_right (hd.parameter_compact.isClosed.prod isClosed_univ)
  have hW : IsOpen W := (hd.primary_open nu).inter (hd.parameter_open.prod isOpen_univ)
  have hCW : C ⊆ W := fun _ hz => hClosure hz.1
  have hCK : C ⊆ Data.parameterSet ×ˢ (univ : Set M) := inter_subset_right
  have hSmoothTransition : ∀ i l, ContDiffOn ℝ ∞ ((chart i).symm.trans (chart l))
      ((chart i).symm.trans (chart l)).source := by
    intro i l
    simpa only [chart,originalJointCoordinateChart_transition,
      originalJointCoordinateChart_transition_source] using
      actualOriginalGivenTransition_contDiffOn Data hd (i,l)
  have hTarget : ∀ i, S i ⊆ (chart i).target := by
    intro i y hy
    rw [originalJointCoordinateChart_target]
    exact hy.1.1
  have hPhysical : ∀ i y, y ∈ S i → (chart i).symm y ∈ C := by
    intro i y hy
    exact ⟨subset_closure hy.2,hy.1.2.2.2,mem_univ _⟩
  have ht : ∀ i l k, 1 ≤ k → ∀ y ∈ S i,
      y ∈ ((chart i).symm.trans (chart l)).source →
      ‖iteratedFDeriv ℝ k ((chart i).symm.trans (chart l)) y‖ ≤ T k := by
    intro i l k hk y hy ho
    rw [originalJointCoordinateChart_transition_source] at ho
    exact hTransition i l k hk y ⟨hy.1,ho⟩
  have hf' : ∀ i, ContDiffOn ℝ ∞ (f ∘ (chart i).symm)
      ((chart i).target ∩ (chart i).symm ⁻¹' W) := by
    intro i
    simpa only [chart,originalJointCoordinateChart_symm,originalJointCoordinateChart_target,
      W,actualOriginalPrimaryCoordinateOpen,incrementsOriginalPrimaryDifferentiation,
      preimage_inter,inter_assoc] using hf i
  exact original_compact_observation_jet_profile_exists chart hSmoothTransition C W hC hW hCW
    (originalJointCoordinateChart_covers Data hd C hCK) S hTarget hPhysical T hT ht f hf'

/-- All weighted norms of the same actual primary coordinate field are
finite after the internal solver annotation is localized. -/
theorem local_primary_field_weighted_finite
    {q : ℕ} (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (nu : Fin Data.primaryCount) (hOpen : IsOpen (domain nu))
    (hCompact : IsCompact (closure (domain nu)))
    (hClosure : closure (domain nu) ⊆
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (hTransition : ∀ i l k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample Data (i,l),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition Data i l) y‖ ≤ T k)
    (f : P × M → Fin q → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞
      (f ∘ incrementsOriginalJointPoint Data.atlas Data.parameterChart i)
      (actualOriginalPrimaryCoordinateOpen Data nu i))
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell
      (fun i => f ∘ incrementsOriginalJointPoint Data.atlas Data.parameterChart i)
      (incrementsOriginalPrimaryDifferentiation (localPrimaryData Data V domain) nu)
      (incrementsOriginalPrimaryEvaluation (localPrimaryData Data V domain) nu) ≠ ⊤ := by
  let D := localPrimaryData Data V domain
  let O := incrementsOriginalPrimaryDifferentiation D nu
  let S := incrementsOriginalPrimaryEvaluation D nu
  let U := fun i => O i ∩ actualOriginalPrimaryCoordinateOpen Data nu i
  have hO : ∀ i, IsOpen (O i) := by
    intro i
    exact (actual_original_jointPoint_continuousOn Data i).isOpen_inter_preimage
      (parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart i) hOpen
  have hU : ∀ i, IsOpen (U i) := fun i =>
    (hO i).inter (actualOriginalPrimaryCoordinateOpen_isOpen Data hd nu i)
  have hSU : ∀ i, S i ⊆ U i := by
    intro i y hy
    exact ⟨⟨hy.1.1,hy.2⟩,⟨hy.1.1,(hClosure (subset_closure hy.2)).1⟩,
      hd.parameter_subset hy.1.2.2.2,mem_univ _⟩
  rw [actual_paperAtlasWeighted_open_restrict base j ell
    (fun i => f ∘ incrementsOriginalJointPoint Data.atlas Data.parameterChart i)
    O U S hO hU (fun _ => inter_subset_left) hSU]
  obtain ⟨B,hB,hJets⟩ := local_primary_joint_jet_profile Data hd V domain nu
    hCompact hClosure T hT hTransition f hf
  apply paperAtlasWeighted_ne_top base j ell _ U S hU hSU
    (fun i => (hf i).mono inter_subset_right)
  intro i k _
  refine ⟨B k,?_⟩
  rintro _ ⟨y,rfl⟩
  exact hJets i k y y.property

theorem local_primary_cutoff_weighted_finite
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
    paperAtlasWeighted base j ell (incrementsOriginalScalarCoordinates Data (Data.cutoff nu))
      (incrementsOriginalPrimaryDifferentiation (localPrimaryData Data V domain) nu)
      (incrementsOriginalPrimaryEvaluation (localPrimaryData Data V domain) nu) ≠ ⊤ := by
  let cy := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.toContinuousLinearMap
  exact local_primary_field_weighted_finite Data hd V domain nu hOpen hCompact hClosure
    T hT hTransition (cy ∘ Data.cutoff nu)
    (actual_original_primary_field_coordinate_smooth Data hd nu (Data.cutoff nu)
      (hs.cutoff_joint nu) cy) base j ell

theorem local_primary_normal_weighted_finite
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
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal nu))
      (incrementsOriginalPrimaryDifferentiation (localPrimaryData Data V domain) nu)
      (incrementsOriginalPrimaryEvaluation (localPrimaryData Data V domain) nu) ≠ ⊤ := by
  let cy := (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
  exact local_primary_field_weighted_finite Data hd V domain nu hOpen hCompact hClosure
    T hT hTransition (cy ∘ Data.freeNormal nu)
    (actual_original_primary_field_coordinate_smooth Data hd nu (Data.freeNormal nu)
      (hs.normal_joint nu) cy) base j ell

theorem local_primary_phase_jet_profile
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (nu : Fin Data.primaryCount)
    (hCompact : IsCompact (closure (domain nu)))
    (hClosure : closure (domain nu) ⊆
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (hTransition : ∀ i l k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample Data (i,l),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition Data i l) y‖ ≤ T k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ i k y, y ∈ incrementsOriginalPrimaryEvaluation (localPrimaryData Data V domain) nu i →
        ‖iteratedFDeriv ℝ k (actualOriginalJointPhase Data nu i) y‖ ≤ C k := by
  apply local_primary_joint_jet_profile Data hd V domain nu hCompact hClosure
    T hT hTransition (Data.phase nu)
  intro i
  apply (actualOriginalJointPhase_contDiffOn Data hd hs nu i).mono
  intro y hy
  exact ⟨hy.1,hy.1.1,hy.2⟩

end GlobalEmbedding.Continuation.FaithfulIncrements
#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.local_primary_joint_jet_profile
#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.local_primary_cutoff_weighted_finite
#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.local_primary_normal_weighted_finite
#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.local_primary_phase_jet_profile

