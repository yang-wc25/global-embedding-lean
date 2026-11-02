import Probes.ActualIncrementOriginalSampling
import Smoothing.TensorPreparedProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Bundle Filter
open scoped ContDiff Topology BigOperators TensorProduct ENNReal Classical
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance marginSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance marginSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ}
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

variable {P : Type*} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

private local instance adaptedGeometryFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
private local instance adaptedGeometryT0Normed : NormedAddCommGroup (D →L[ℝ] Tdata) := inferInstance
private local instance adaptedGeometryT0Space : NormedSpace ℝ (D →L[ℝ] Tdata) := inferInstance
private local instance marginCdataNormed : NormedAddCommGroup (Fin (m+1) → ℂ) := inferInstance
private local instance marginCdataSpace : NormedSpace ℝ (Fin (m+1) → ℂ) := inferInstance
private local instance marginCjetNormed : NormedAddCommGroup (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCjetSpace : NormedSpace ℝ (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance marginCANormed : NormedAddCommGroup
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCASpace : NormedSpace ℝ
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance marginCBNormed : NormedAddCommGroup
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCBSpace : NormedSpace ℝ
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedSpace

private local instance rawCoeffInnerNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private local instance rawCoeffInnerSpace : NormedSpace ℝ
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance rawCoeffOuterNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance rawCoeffOuterSpace : NormedSpace ℝ
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable {Β : Type*} [Fintype Β]


/-- The literal squared normalized source cutoffs already used by the
actual smoother are an ordinary parent partition for adapted refinements.
Their relative support is inside the ORIGINAL inner domains for every W;
no compactness of the source manifold is used. -/
theorem actual_original_prepared_parent_cutoffs
    (A : BufferedAtlas M D) (B0 T : ℕ → ℝ) (degree : ℕ)
    (RS : TensorRawCutoffPreparation A B0 T degree) :
    let theta := fun i (z : Ep × M) => squareNormalizedCutoff RS.raw i z.2 ^ 2
    (∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i)) ∧
    (∀ z, ∑ i, theta i z = 1) ∧
    ∀ (W : Set (Ep × M)) i z, z ∈ incrementsGlobalRelativeSupport W (theta i) →
      z.2 ∈ A.inner i := by
  intro theta
  have hpos := fun x => one_le_squareCutoffSum_of_plateau RS.raw x (RS.plateau_cover x)
  refine ⟨?_,?_,?_⟩
  · intro i
    exact (contDiff_id.pow 2).comp_contMDiff
      ((squareNormalizedCutoff_contMDiff RS.raw RS.smooth hpos i).comp contMDiff_snd)
  · intro z
    exact squareNormalizedCutoff_sum_sq RS.raw z.2 (zero_lt_one.trans_le (hpos z.2))
  · intro W i z hz
    obtain ⟨w,hw,rfl⟩ := hz
    have hsupport : tsupport (fun v : W => theta i v.val) ⊆
        (fun v : W => v.val.2) ⁻¹' tsupport (squareNormalizedCutoff RS.raw i) := by
      apply closure_minimal _ ((isClosed_tsupport _).preimage (continuous_snd.comp continuous_subtype_val))
      intro v hv
      apply subset_tsupport
      intro hzero
      apply hv
      change squareNormalizedCutoff RS.raw i v.val.2 ^ 2 = 0
      change squareNormalizedCutoff RS.raw i v.val.2 = 0 at hzero
      rw [hzero]
      norm_num
    exact RS.inner_support i (squareNormalizedCutoff_tsupport_subset RS.raw i (hsupport hw))

theorem actualOriginalPrimaryFamily_original_samples_from_prepared_parent
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M D)
    (hdata : ∀ nu beta, ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b nu beta)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu beta))
    (eta : Fin Data.primaryCount → Β → Ep × M → ℝ)
    (hactive : ∀ nu beta w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (B0 T : ℕ → ℝ) (degree : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas B0 T degree)
    (G : Set (P × M)) (hG : IsOpen G) (observer : Fin Data.atlas.count) :
    let F := actualOriginalOpenParameterSlice Data i
    let g0 := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    let W := actualOriginalParameterNeighborhood Data i.2 G
    let hW := actualOriginalParameterNeighborhood_isOpen Data i.2 G hG
    let g := parameterRound2_restrictPrimaryFamily F g0 W hW
    let obs := Data.atlas.chart observer
    let a := parameterTensorModelEquiv (m+1) d
    let kappa := fun z : X => (z.1,obs.symm z.2)
    let S := a ⁻¹' incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
      Data.parameterNormDomain Data.parameterSet (observer,i.2)
    let R := fun nu => S ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff nu)
    let Rloc := fun nu beta => R nu ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W
      (fun z => g.eta nu beta z*g.cutoff nu z)
    let Sloc := fun nu beta => (g.chart nu beta ∘ kappa) '' Rloc nu beta
    (hEtaSupport : ∀ nu beta, incrementsGlobalRelativeSupport W (eta nu beta) ⊆ (g0.chart nu beta).source) →
    (hEtaParent : ∀ nu beta, incrementsGlobalRelativeSupport W (eta nu beta) ⊆
      incrementsGlobalRelativeSupport W
        (fun z : Ep × M => squareNormalizedCutoff RS.raw (host nu beta) z.2 ^ 2)) →
    ∀ nu beta, MapsTo (b nu beta).symm (Sloc nu beta) (a ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet (host nu beta,i.2)) := by
  intro F g0 W hW g obs a kappa S R Rloc Sloc hEtaSupport hEtaParent
  apply actualOriginalPrimaryFamily_original_samples_of_inner_support Data hd hs hn i host b e hdata
    eta hactive G hG observer hEtaSupport
  intro nu beta w hw
  exact (actual_original_prepared_parent_cutoffs (d := d) Data.atlas B0 T degree RS).2.2
    W (host nu beta) w (hEtaParent nu beta hw)

#print axioms actual_original_prepared_parent_cutoffs
#print axioms actualOriginalPrimaryFamily_original_samples_from_prepared_parent
end GlobalEmbedding.Continuation
