import FaithfulRepair.OriginalMapFiniteness
import Smoothing.TensorNativeTransitions

/-!
# Both original tensor frames on full original chart overlaps

The coordinate tensor changes basis in both source tangent slots.  The
actual frame coefficients are proved to be the source transition Jacobian,
including all positive total parameter/source derivatives.  Their bounds
come from the original next source-transition derivative, with the actual
fixed source projection norm retained.  No frame budget is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Module Filter
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulRepair

section LinearPrecomposition
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The actual linear source projection needs only local smoothness. -/
theorem norm_iteratedFDeriv_comp_linear_local
    (L : E →L[ℝ] F) (f : F → G) (O : Set F) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (x : E) (hx : L x ∈ O) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ * ‖L‖^k := by
  have hU : IsOpen (L ⁻¹' O) := hO.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf hO.uniqueDiffOn hU.uniqueDiffOn hx (i := k) (by simp)
  rw [iteratedFDerivWithin_of_isOpen k hU hx,iteratedFDerivWithin_of_isOpen k hO hx] at he
  rw [he]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ k f (L x)) (fun _ => L)
end LinearPrecomposition

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- Full actual source overlap, with no artificial host-inner restriction. -/
theorem original_source_frame_eq_fderiv
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))) (hA : IsSmoothBufferedAtlas A)
    (p i : Fin A.count) (a r : Fin n) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ ((A.chart p).symm.trans (A.chart i)).source) :
    tensorFrameTransition A (bufferedNativeTensorFrame A hA) p i a r y =
      (fderiv ℝ (A.chart i ∘ (A.chart p).symm) y (EuclideanSpace.single a 1)) r := by
  classical
  have hi : (A.chart p).symm y ∈ (A.chart i).source := hy.2
  unfold tensorFrameTransition
  rw [bufferedNativeTensorFrame_at_inverse A hA p y hy.1,
    bufferedSourceChartBasis_apply A hA p y hy.1]
  unfold bufferedNativeTensorFrame
  simp only [dite_eq_left hi,Basis.map_repr,LinearEquiv.trans_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,EuclideanSpace.basisFun_repr]
  have hc := mfderiv_comp y ((bufferedChartMDifferentiable A hA i).mdifferentiableAt hi)
    ((bufferedChartMDifferentiable A hA p).mdifferentiableAt_symm hy.1)
  rw [mfderiv_eq_fderiv] at hc
  have hce := congrArg (fun L =>
    (L ((tangentSpaceCastModel 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) y).symm
      (EuclideanSpace.single a 1)) : EuclideanSpace ℝ (Fin n)) r) hc
  exact hce.symm

/-- The literal projection to the source part of the original joint vector. -/
def originalSourceProjection (n d : ℕ) : (Fin (n+d) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n))).comp
    (parameterTensorModelEquiv n d).symm.toContinuousLinearMap

@[simp] theorem originalSourceProjection_apply (y : Fin (n+d) → ℝ) :
    originalSourceProjection n d y = incrementsOriginalSourcePoint y := rfl

/-- This is the actual change between the same two source tangent bases. -/
def originalTensorFrameEntry
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (p i : Fin D.atlas.count × Fin D.parameterCount) (a r : Fin n)
    (y : Fin (n+d) → ℝ) : ℝ :=
  tensorFrameTransition D.atlas (bufferedNativeTensorFrame D.atlas hd.atlas_smooth)
    p.1 i.1 a r (incrementsOriginalSourcePoint y)

theorem originalTensorFrameEntry_contDiffOn
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (p i : Fin D.atlas.count × Fin D.parameterCount) (a r : Fin n) :
    ContDiffOn ℝ ∞ (originalTensorFrameEntry D hd p i a r)
      (actualOriginalGivenTransitionDomain D (p,i)) := by
  let e := (D.atlas.chart p.1).symm.trans (D.atlas.chart i.1)
  have he : ContDiffOn ℝ ∞ e e.source :=
    (round3Parameter_partial_trans_smooth (D.atlas.chart p.1).symm (D.atlas.chart i.1)
      (contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem p.1))
      (contMDiffOn_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1))).contDiffOn
  have hder := he.fderiv_of_isOpen e.open_source (m := ∞) (by simp)
  have hlocal : ContDiffOn ℝ ∞ (tensorJacobianEntryCLM a r ∘ fderiv ℝ e) e.source :=
    (tensorJacobianEntryCLM a r).contDiff.comp_contDiffOn hder
  have hmap : MapsTo (originalSourceProjection n d) (actualOriginalGivenTransitionDomain D (p,i))
      e.source := fun _ hy => ⟨hy.1.1,hy.2.2⟩
  apply (hlocal.comp (originalSourceProjection n d).contDiff.contDiffOn hmap).congr
  intro y hy
  exact original_source_frame_eq_fderiv D.atlas hd.atlas_smooth p.1 i.1 a r (hmap hy)

/-- The next original source-transition derivative bounds every total jet
of the genuine frame entry, with the fixed projection norm explicit. -/
theorem originalTensorFrameEntry_jet_le
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (p i : Fin D.atlas.count × Fin D.parameterCount) (a r : Fin n)
    (y : Fin (n+d) → ℝ) (hy : y ∈ actualOriginalGivenTransitionDomain D (p,i)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (originalTensorFrameEntry D hd p i a r) y‖ ≤
      ‖iteratedFDeriv ℝ (k+1) ((D.atlas.chart p.1).symm.trans (D.atlas.chart i.1))
        (incrementsOriginalSourcePoint y)‖ * ‖originalSourceProjection n d‖^k := by
  let e := (D.atlas.chart p.1).symm.trans (D.atlas.chart i.1)
  let L := originalSourceProjection n d
  have he : ContDiffOn ℝ ∞ e e.source :=
    (round3Parameter_partial_trans_smooth (D.atlas.chart p.1).symm (D.atlas.chart i.1)
      (contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem p.1))
      (contMDiffOn_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1))).contDiffOn
  have hder := he.fderiv_of_isOpen e.open_source (m := ∞) (by simp)
  have hLy : L y ∈ e.source := ⟨hy.1.1,hy.2.2⟩
  have hlocal : ContDiffOn ℝ ∞ (tensorJacobianEntryCLM a r ∘ fderiv ℝ e) e.source :=
    (tensorJacobianEntryCLM a r).contDiff.comp_contDiffOn hder
  have hEq : originalTensorFrameEntry D hd p i a r =ᶠ[𝓝 y]
      (tensorJacobianEntryCLM a r ∘ fderiv ℝ e) ∘ L := by
    filter_upwards [(actualOriginalGivenTransitionDomain_open D (p,i)).mem_nhds hy] with z hz
    exact original_source_frame_eq_fderiv D.atlas hd.atlas_smooth p.1 i.1 a r ⟨hz.1.1,hz.2.2⟩
  rw [(hEq.iteratedFDeriv ℝ k).eq_of_nhds]
  apply (norm_iteratedFDeriv_comp_linear_local L _ e.source e.open_source hlocal y hLy k).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
  have hpost := (tensorJacobianEntryCLM a r).norm_iteratedFDeriv_comp_left
    (hder.contDiffAt (e.open_source.mem_nhds hLy)) (n := k) (by simp)
  apply hpost.trans
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_of_le_one_left (norm_nonneg _) (tensorJacobianEntryCLM_norm_le a r)

end GlobalEmbedding.Continuation.FaithfulRepair

#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_source_frame_eq_fderiv
#print axioms GlobalEmbedding.Continuation.FaithfulRepair.originalTensorFrameEntry_contDiffOn
#print axioms GlobalEmbedding.Continuation.FaithfulRepair.originalTensorFrameEntry_jet_le
