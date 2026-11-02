import OriginalIntegration.OriginalNormComparison
import FaithfulRepair.OriginalTransitionFiniteness
import Smoothing.Round3OuterOriginalEllipticityStability

/-!
# Original source/parameter chart norms from actual inner-cover samples

The comparison uses the paper's source-first coordinate functions verbatim.
Both the source and parameter chart counts are absent from its cost.  The
internal domains KS/KP only have to contain the actual inner samples of the
same buffered charts.  They are not substituted for the public Omega/Q.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.OriginalIntegration

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

def atlasJointChart (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (i : Fin A.count × Fin B.count) : OpenPartialHomeomorph (P × M) (Fin (n+d) → ℝ) :=
  ((B.chart i.2).prod (A.chart i.1)).trans
    (parameterTensorModelEquiv n d).toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem atlasJointChart_symm (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (i : Fin A.count × Fin B.count) :
    ⇑(atlasJointChart A B i).symm = incrementsOriginalJointPoint A B.chart i := rfl

@[simp] theorem atlasJointChart_source (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (i : Fin A.count × Fin B.count) :
    (atlasJointChart A B i).source = (B.chart i.2).source ×ˢ (A.chart i.1).source := by
  ext x
  simp only [atlasJointChart,OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source,preimage_univ,inter_univ]
  rfl

@[simp] theorem atlasJointChart_target (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (i : Fin A.count × Fin B.count) :
    (atlasJointChart A B i).target = incrementsOriginalDifferentiation A B.chart i := by
  ext y
  change (y ∈ (univ : Set (Fin (n+d) → ℝ)) ∧
    (parameterTensorModelEquiv n d).symm y ∈ (B.chart i.2).target ×ˢ (A.chart i.1).target) ↔ _
  simp only [mem_univ,true_and,parameterTensorModelEquiv_symm_apply,mem_prod,
    incrementsOriginalDifferentiation,mem_ofPred_eq]
  exact and_comm

theorem atlasJointChart_inner_cover (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (Omega KS : Fin A.count → Set Es) (Q KP : Fin B.count → Set Ep)
    (hKS : ∀ i, bufferedSamplingCoordinates A i ⊆ KS i)
    (hKP : ∀ i, bufferedSamplingCoordinates B i ⊆ KP i) :
    ∀ i y, y ∈ incrementsOriginalEvaluation A B.chart Omega Q univ i → ∃ l,
      (atlasJointChart A B i).symm y ∈ (atlasJointChart A B l).source ∧
      atlasJointChart A B l ((atlasJointChart A B i).symm y) ∈
        incrementsOriginalEvaluation A B.chart KS KP univ l := by
  intro i y hy
  let z := incrementsOriginalJointPoint A B.chart i y
  obtain ⟨s,hs⟩ := A.cover z.2
  obtain ⟨p,hp⟩ := B.cover z.1
  refine ⟨(s,p),?_,?_⟩
  · rw [atlasJointChart_source]
    exact ⟨B.inner_subset p hp,A.inner_subset s hs⟩
  · have he := (parameterTensorModelEquiv n d).symm_apply_apply (B.chart p z.1,A.chart s z.2)
    have hparam := congrArg Prod.fst he
    have hsource := congrArg Prod.snd he
    change incrementsOriginalParameterPoint (parameterTensorModelEquiv n d
      (B.chart p z.1,A.chart s z.2)) = B.chart p z.1 at hparam
    change incrementsOriginalSourcePoint (parameterTensorModelEquiv n d
      (B.chart p z.1,A.chart s z.2)) = A.chart s z.2 at hsource
    change parameterTensorModelEquiv n d (B.chart p z.1,A.chart s z.2) ∈
      incrementsOriginalEvaluation A B.chart KS KP univ (s,p)
    change (incrementsOriginalSourcePoint (parameterTensorModelEquiv n d
        (B.chart p z.1,A.chart s z.2)) ∈ (A.chart s).target ∧
      incrementsOriginalParameterPoint (parameterTensorModelEquiv n d
        (B.chart p z.1,A.chart s z.2)) ∈ (B.chart p).target) ∧
      incrementsOriginalSourcePoint (parameterTensorModelEquiv n d
        (B.chart p z.1,A.chart s z.2)) ∈ KS s ∧
      incrementsOriginalParameterPoint (parameterTensorModelEquiv n d
        (B.chart p z.1,A.chart s z.2)) ∈ KP p ∧ _
    rw [hparam,hsource]
    exact ⟨⟨(A.chart s).map_source (A.inner_subset s hs),
      (B.chart p).map_source (B.inner_subset p hp)⟩,
      hKS s (bufferedInner_subset_sampling A s (bufferedInnerCoordinates_mem A s hs)),
      hKP p (bufferedInner_subset_sampling B p (bufferedInnerCoordinates_mem B p hp)),mem_univ _⟩

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

private local instance atlasNormProductChart : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
private local instance atlasNormProductManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

theorem atlasJointChart_transition_smooth (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B) :
    ∀ i l, ContDiffOn ℝ ∞ ((atlasJointChart A B i).symm.trans (atlasJointChart A B l))
      ((atlasJointChart A B i).symm.trans (atlasJointChart A B l)).source := by
  intro i l
  let a := parameterTensorModelEquiv n d
  let qi := (B.chart i.2).prod (A.chart i.1)
  let ql := (B.chart l.2).prod (A.chart l.1)
  have hqi : qi ∈ maximalAtlas 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact mem_maximalAtlas_prod (hB.chart_mem i.2) (hA.chart_mem i.1)
  have hql : ql ∈ maximalAtlas 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact mem_maximalAtlas_prod (hB.chart_mem l.2) (hA.chart_mem l.1)
  let : ChartedSpace (Ep × Es) (Ep × Es) := chartedSpaceSelf (Ep × Es)
  have ht : ContDiffOn ℝ ∞ (ql ∘ qi.symm) (qi.target ∩ qi.symm ⁻¹' ql.source) :=
    ((contMDiffOn_of_mem_maximalAtlas hql).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hqi).mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn
  change ContDiffOn ℝ ∞ (a ∘ (ql ∘ qi.symm) ∘ a.symm) _
  apply a.contDiff.comp_contDiffOn (ht.comp a.symm.contDiff.contDiffOn ?_)
  intro y hy
  have hh : y ∈ (atlasJointChart A B i).target ∧
      (atlasJointChart A B i).symm y ∈ (atlasJointChart A B l).source := hy
  rw [atlasJointChart_target,atlasJointChart_source] at hh
  exact ⟨⟨hh.1.2,hh.1.1⟩,hh.2⟩

/-- The original separate total parameter/source transition jets supply the
same source-first joint budget, including its true Euclidean/Pi factors. -/
theorem atlasJointChart_transition_bound
    (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (Omega : Fin A.count → Set Es) (Q : Fin B.count → Set Ep)
    (Parameter Spatial : ℕ → ℝ)
    (hParam : ∀ ip jp k, 1 ≤ k → ∀ z : Ep × Es, z.1 ∈ Q ip →
      z ∈ (((B.chart ip).symm.trans (B.chart jp)).prod (OpenPartialHomeomorph.refl Es)).source →
      ‖iteratedFDeriv ℝ k (((B.chart ip).symm.trans (B.chart jp)).prod
        (OpenPartialHomeomorph.refl Es)) z‖ ≤ Parameter k)
    (hSpatial : ∀ i l k, 1 ≤ k → ∀ z : Ep × Es, z.2 ∈ Omega i →
      z ∈ ((OpenPartialHomeomorph.refl Ep).prod ((A.chart i).symm.trans (A.chart l))).source →
      ‖iteratedFDeriv ℝ k ((OpenPartialHomeomorph.refl Ep).prod
        ((A.chart i).symm.trans (A.chart l))) z‖ ≤ Spatial k) :
    ∀ i l k, 1 ≤ k → ∀ y ∈ incrementsOriginalEvaluation A B.chart Omega Q univ i,
      y ∈ ((atlasJointChart A B i).symm.trans (atlasJointChart A B l)).source →
      ‖iteratedFDeriv ℝ k ((atlasJointChart A B i).symm.trans (atlasJointChart A B l)) y‖ ≤
        FaithfulRepair.originalJointTransitionProfile n d Parameter Spatial k := by
  intro i l k hk y hy hyOverlap
  let a := parameterTensorModelEquiv n d
  let z := a.symm y
  let ep := (B.chart i.2).symm.trans (B.chart l.2)
  let es := (A.chart i.1).symm.trans (A.chart l.1)
  let e := ep.prod es
  have hh : y ∈ (atlasJointChart A B i).target ∧
      (atlasJointChart A B i).symm y ∈ (atlasJointChart A B l).source := hyOverlap
  rw [atlasJointChart_target,atlasJointChart_source] at hh
  have hp : z.1 ∈ ep.source := ⟨hh.1.2,hh.2.1⟩
  have hs : z.2 ∈ es.source := ⟨hh.1.1,hh.2.2⟩
  have hps : ContDiffOn ℝ ∞ ep ep.source :=
    (round3Parameter_partial_trans_smooth _ _
      (contMDiffOn_symm_of_mem_maximalAtlas (hB.chart_mem _))
      (contMDiffOn_of_mem_maximalAtlas (hB.chart_mem _))).contDiffOn
  have hss : ContDiffOn ℝ ∞ es es.source :=
    (round3Parameter_partial_trans_smooth _ _
      (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem _))
      (contMDiffOn_of_mem_maximalAtlas (hA.chart_mem _))).contDiffOn
  have he : ContDiffOn ℝ ∞ e e.source := hps.prodMap hss
  have hz : z ∈ e.source := ⟨hp,hs⟩
  have hn : ‖iteratedFDeriv ℝ k e z‖ ≤ max (Parameter k) (Spatial k) :=
    AuxNormBridge.joint_jet_le_partial_product_max ep es z
      (hps.contDiffAt (ep.open_source.mem_nhds hp))
      (hss.contDiffAt (es.open_source.mem_nhds hs)) k _ _
      (hParam i.2 l.2 k hk z hy.2.2.1 ⟨hp,mem_univ _⟩)
      (hSpatial i.1 l.1 k hk z hy.2.1 ⟨mem_univ _,hs⟩)
  have hpre := norm_iteratedFDeriv_comp_equiv_le a.symm e k y
  have hsm : ContDiffAt ℝ ∞ (e ∘ a.symm) y :=
    (he.contDiffAt (e.open_source.mem_nhds hz)).comp y a.symm.contDiff.contDiffAt
  have hpost := a.toContinuousLinearMap.norm_iteratedFDeriv_comp_left hsm (n := k) (by simp)
  change ‖iteratedFDeriv ℝ k (a ∘ e ∘ a.symm) y‖ ≤ _
  apply hpost.trans
  apply (mul_le_mul_of_nonneg_left
    (hpre.trans (mul_le_mul_of_nonneg_right hn (linearModelFactor_nonneg _ _)))
    (norm_nonneg _)).trans_eq
  dsimp only [FaithfulRepair.originalJointTransitionProfile,a]
  ring

theorem original_atlas_norm_le_internal_cover
    (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (Omega KS : Fin A.count → Set Es) (Q KP : Fin B.count → Set Ep)
    (hKS : ∀ i, bufferedSamplingCoordinates A i ⊆ KS i)
    (hKP : ∀ i, bufferedSamplingCoordinates B i ⊆ KP i)
    (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ k, 0 ≤ Parameter k)
    (hParam : ∀ ip jp k, 1 ≤ k → ∀ z : Ep × Es, z.1 ∈ Q ip →
      z ∈ (((B.chart ip).symm.trans (B.chart jp)).prod (OpenPartialHomeomorph.refl Es)).source →
      ‖iteratedFDeriv ℝ k (((B.chart ip).symm.trans (B.chart jp)).prod
        (OpenPartialHomeomorph.refl Es)) z‖ ≤ Parameter k)
    (hSpatial : ∀ i l k, 1 ≤ k → ∀ z : Ep × Es, z.2 ∈ Omega i →
      z ∈ ((OpenPartialHomeomorph.refl Ep).prod ((A.chart i).symm.trans (A.chart l))).source →
      ‖iteratedFDeriv ℝ k ((OpenPartialHomeomorph.refl Ep).prod
        ((A.chart i).symm.trans (A.chart l))) z‖ ≤ Spatial k)
    (F : P × M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,Es)) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F)
    (j : ℕ) :
    paperAtlasCj j (incrementsOriginalMapCoordinates A B.chart F)
      (incrementsOriginalDifferentiation A B.chart)
      (incrementsOriginalEvaluation A B.chart Omega Q univ) ≤
    ENNReal.ofReal (originalCoverNormCost (n+d)
      (FaithfulRepair.originalJointTransitionProfile n d Parameter Spatial) j) *
    paperAtlasCj j (incrementsOriginalMapCoordinates A B.chart F)
      (incrementsOriginalDifferentiation A B.chart)
      (incrementsOriginalEvaluation A B.chart KS KP univ) := by
  have h := original_norm_le_cover_norm (atlasJointChart A B)
    (atlasJointChart_transition_smooth A B hA hB)
    (incrementsOriginalEvaluation A B.chart Omega Q univ)
    (incrementsOriginalEvaluation A B.chart KS KP univ)
    (fun i y hy => (atlasJointChart_target A B i).symm ▸ hy.1)
    (fun i y hy => (atlasJointChart_target A B i).symm ▸ hy.1)
    (atlasJointChart_inner_cover A B Omega KS Q KP hKS hKP)
    (FaithfulRepair.originalJointTransitionProfile n d Parameter Spatial)
    (FaithfulRepair.originalJointTransitionProfile_nonneg n d Parameter Spatial hParameter)
    (atlasJointChart_transition_bound A B hA hB Omega Q Parameter Spatial hParam hSpatial)
    ((EuclideanSpace.equiv (Fin N) ℝ) ∘ F)
    (fun i => by
      rw [atlasJointChart_target,atlasJointChart_symm]
      change ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart F i)
        (incrementsOriginalDifferentiation A B.chart i)
      exact round3_original_map_coordinates_contDiffOn A B.chart hA hB.chart_mem F hF i) j
  simp only [atlasJointChart_target,atlasJointChart_symm] at h
  change paperAtlasCj j (incrementsOriginalMapCoordinates A B.chart F)
    (incrementsOriginalDifferentiation A B.chart)
    (incrementsOriginalEvaluation A B.chart Omega Q univ) ≤ _ at h
  exact h

end GlobalEmbedding.Continuation.OriginalIntegration

#print axioms GlobalEmbedding.Continuation.OriginalIntegration.original_atlas_norm_le_internal_cover
