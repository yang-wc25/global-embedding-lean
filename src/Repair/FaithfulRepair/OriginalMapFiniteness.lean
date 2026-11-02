import FaithfulRepair.OriginalJetFiniteness
import Probes.ActualOriginalTransitionProfileJets

/-!
# Literal original joint norms from compact physical observations

The original product charts are presented in their unchanged source-first
Pi coordinates.  Compactness is used only for the actual physical parameter
set times the source, never for Omega or Q.  The given map and all its norm
domains are retained verbatim.  The original transition budget is an input
geometry primitive; no finiteness of the desired input profile is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Continuation.FaithfulRepair

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- Precisely the original product chart, in the original source-first
coordinate presentation.  This changes no underlying map or norm. -/
def originalJointCoordinateChart (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    OpenPartialHomeomorph (P × M) (Fin (n+d) → ℝ) :=
  ((D.parameterChart i.2).prod (D.atlas.chart i.1)).trans
    (parameterTensorModelEquiv n d).toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem originalJointCoordinateChart_symm
    (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    ⇑(originalJointCoordinateChart D i).symm =
      incrementsOriginalJointPoint D.atlas D.parameterChart i := rfl

@[simp] theorem originalJointCoordinateChart_source
    (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    (originalJointCoordinateChart D i).source =
      (D.parameterChart i.2).source ×ˢ (D.atlas.chart i.1).source := by
  ext x
  simp only [originalJointCoordinateChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
  rfl

@[simp] theorem originalJointCoordinateChart_target
    (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    (originalJointCoordinateChart D i).target =
      incrementsOriginalDifferentiation D.atlas D.parameterChart i := by
  ext y
  change (y ∈ (univ : Set (Fin (n+d) → ℝ)) ∧
    (parameterTensorModelEquiv n d).symm y ∈
      (D.parameterChart i.2).target ×ˢ (D.atlas.chart i.1).target) ↔ _
  simp only [mem_univ, true_and, parameterTensorModelEquiv_symm_apply, mem_prod,
    incrementsOriginalDifferentiation, mem_ofPred_eq]
  exact and_comm

@[simp] theorem originalJointCoordinateChart_transition
    (D : IncrementsOriginalNativeData n d N M P)
    (i k : Fin D.atlas.count × Fin D.parameterCount) :
    ⇑((originalJointCoordinateChart D i).symm.trans (originalJointCoordinateChart D k)) =
      actualOriginalGivenTransition D i k := rfl

@[simp] theorem originalJointCoordinateChart_transition_source
    (D : IncrementsOriginalNativeData n d N M P)
    (i k : Fin D.atlas.count × Fin D.parameterCount) :
    ((originalJointCoordinateChart D i).symm.trans (originalJointCoordinateChart D k)).source =
      actualOriginalGivenTransitionDomain D (i,k) := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    originalJointCoordinateChart_target, originalJointCoordinateChart_symm,
    originalJointCoordinateChart_source]
  rfl

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- A compact physical observation set is covered by the original chart
family, using only the original compact-parameter covering clause. -/
theorem originalJointCoordinateChart_covers
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (C : Set (P × M)) (hCK : C ⊆ D.parameterSet ×ˢ (univ : Set M)) :
    ∀ z ∈ C, ∃ i, z ∈ (originalJointCoordinateChart D i).source := by
  intro z hz
  obtain ⟨p,hp,_⟩ := hd.parameter_cover z.1 (hCK hz).1
  obtain ⟨s,hs⟩ := D.atlas.cover z.2
  refine ⟨(s,p),?_⟩
  rw [originalJointCoordinateChart_source]
  exact ⟨hp,D.atlas.inner_subset s hs⟩

/-- Finiteness is produced for the literal original chart maximum on any
unchanged samples in a compact physical carrier.  The open differentiation
domains may be the original whole domains or actual primary domains. -/
theorem original_joint_field_weighted_finite [R1Space M] [R1Space P]
    {q : ℕ} (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (C W : Set (P × M)) (hC : IsCompact C) (hW : IsOpen W) (hCW : C ⊆ W)
    (hCK : C ⊆ D.parameterSet ×ˢ (univ : Set M))
    (O S : (Fin D.atlas.count × Fin D.parameterCount) → Set (Fin (n+d) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hSample : ∀ i, S i ⊆ incrementsOriginalEvaluation D.atlas D.parameterChart
      D.sourceNormDomain D.parameterNormDomain D.parameterSet i)
    (hPhysical : ∀ i y, y ∈ S i → incrementsOriginalJointPoint D.atlas D.parameterChart i y ∈ C)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (hTransition : ∀ i l k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample D (i,l),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition D i l) y‖ ≤ T k)
    (f : P × M → Fin q → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f ∘ incrementsOriginalJointPoint D.atlas D.parameterChart i)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart i ∩
        (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹' W))
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell
      (fun i => f ∘ incrementsOriginalJointPoint D.atlas D.parameterChart i) O S ≠ ⊤ := by
  let chart := originalJointCoordinateChart D
  have hSmoothTransition : ∀ i l, ContDiffOn ℝ ∞ ((chart i).symm.trans (chart l))
      ((chart i).symm.trans (chart l)).source := by
    intro i l
    simpa only [chart,originalJointCoordinateChart_transition,
      originalJointCoordinateChart_transition_source] using
      actualOriginalGivenTransition_contDiffOn D hd (i,l)
  have hTarget : ∀ i, S i ⊆ (chart i).target := by
    intro i y hy
    rw [originalJointCoordinateChart_target]
    exact (hSample i hy).1
  have ht : ∀ i l k, 1 ≤ k → ∀ y ∈ S i,
      y ∈ ((chart i).symm.trans (chart l)).source →
      ‖iteratedFDeriv ℝ k ((chart i).symm.trans (chart l)) y‖ ≤ T k := by
    intro i l k hk y hy ho
    rw [originalJointCoordinateChart_transition_source] at ho
    exact hTransition i l k hk y ⟨hSample i hy,ho⟩
  have hf' : ∀ i, ContDiffOn ℝ ∞ (f ∘ (chart i).symm)
      ((chart i).target ∩ (chart i).symm ⁻¹' W) := by
    simpa only [chart,originalJointCoordinateChart_symm,originalJointCoordinateChart_target] using hf
  obtain ⟨B,hB,hJets⟩ := original_compact_observation_jet_profile_exists chart hSmoothTransition
    C W hC hW hCW (originalJointCoordinateChart_covers D hd C hCK) S hTarget hPhysical T hT ht f hf'
  let U := fun i => O i ∩ ((chart i).target ∩ (chart i).symm ⁻¹' W)
  have hU : ∀ i, IsOpen (U i) := fun i => (hO i).inter
    ((chart i).symm.continuousOn.isOpen_inter_preimage (chart i).open_target hW)
  have hSU : ∀ i, S i ⊆ U i := fun i y hy =>
    ⟨hSO i hy,hTarget i hy,hCW (hPhysical i y hy)⟩
  rw [actual_paperAtlasWeighted_open_restrict base j ell
    (fun i => f ∘ incrementsOriginalJointPoint D.atlas D.parameterChart i) O U S
    hO hU (fun _ => inter_subset_left) hSU]
  apply paperAtlasWeighted_ne_top base j ell _ U S hU hSU
    (fun i => (hf' i).mono inter_subset_right)
  intro i k _
  refine ⟨B k,?_⟩
  rintro _ ⟨y,rfl⟩
  exact hJets i k y y.property

/-- The same original background map has all weighted input norms finite.
The compact physical carrier is manufactured as K × M; neither original
coordinate norm piece is required to be compact. -/
theorem original_map_weighted_finite [R1Space M] [R1Space P] [CompactSpace M]
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (hTransition : ∀ i l k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample D (i,l),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition D i l) y‖ ≤ T k)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell (incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet) ≠ ⊤ := by
  exact original_joint_field_weighted_finite D hd (D.parameterSet ×ˢ (univ : Set M))
    (incrementsOriginalParameterRegion D) (hd.parameter_compact.prod isCompact_univ)
    (hd.parameter_open.prod isOpen_univ) (fun _ hz => ⟨hd.parameter_subset hz.1,hz.2⟩)
    Subset.rfl _ _ (parameterRound2_originalDifferentiation_open D.atlas D.parameterChart)
    (fun _ _ hz => hz.1) (fun _ => Subset.rfl) (fun _ _ hz => ⟨hz.2.2.2,mem_univ _⟩)
    T hT hTransition ((EuclideanSpace.equiv (Fin N) ℝ) ∘ D.F)
    (actual_original_map_coordinates_parameter_open D hd hs) base j ell

end GlobalEmbedding.Continuation.FaithfulRepair

#print axioms GlobalEmbedding.Continuation.FaithfulRepair.originalJointCoordinateChart_covers
#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_joint_field_weighted_finite
#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_map_weighted_finite
