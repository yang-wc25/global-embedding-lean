import Probes.ActualIncrementOriginalNativeRawProducer
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


theorem actual_original_native_evaluation_iff
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : X) :
    parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i ↔
    z.2 ∈ Data.sourceNormDomain i.1 ∧ z.1 ∈ Data.parameterNormDomain i.2 ∧
      (Data.parameterChart i.2).symm z.1 ∈ Data.parameterSet := by
  have hpair : (incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z),
      incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z)) = z :=
    (parameterTensorModelEquiv (m+1) d).symm_apply_apply z
  have hp := congrArg Prod.fst hpair
  have hx := congrArg Prod.snd hpair
  dsimp only at hp hx
  simp only [incrementsOriginalEvaluation, incrementsOriginalDifferentiation, mem_setOf_eq,
    incrementsOriginalJointPoint, hp, hx]
  exact ⟨fun h => h.2,fun h => ⟨⟨hd.source_norm_subset i.1 h.1,hd.parameter_norm_subset i.2 h.2.1⟩,h⟩⟩

theorem actualOriginalPrimaryFamily_original_samples_of_inner_support
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
    (hEtaInner : ∀ nu beta w, w ∈ incrementsGlobalRelativeSupport W (eta nu beta) →
      w.2 ∈ Data.atlas.inner (host nu beta)) →
    ∀ nu beta, MapsTo (b nu beta).symm (Sloc nu beta) (a ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet (host nu beta,i.2)) := by
  intro F g0 W hW g obs a kappa S R Rloc Sloc hEtaSupport hEtaInner nu beta
  rintro y ⟨z,hz,rfl⟩
  have hEta : kappa z ∈ incrementsGlobalRelativeSupport W (eta nu beta) := by
    obtain ⟨w,hw,heq⟩ := hz.2
    exact ⟨w,tsupport_mul_subset_left hw,heq⟩
  have hsrc := hEtaSupport nu beta hEta
  have hbeq : (b nu beta).symm ((g.chart nu beta ∘ kappa) z) =
      (z.1,Data.atlas.chart (host nu beta) (obs.symm z.2)) := by
    exact (b nu beta).left_inv hsrc.2
  rw [hbeq]
  apply (actual_original_native_evaluation_iff Data hd (host nu beta,i.2) _).mpr
  have hobs := (actual_original_native_evaluation_iff Data hd (observer,i.2) z).mp hz.1.1
  exact ⟨hd.source_inner_norm (host nu beta) _ (hEtaInner nu beta _ hEta),hobs.2⟩

#print axioms actual_original_native_evaluation_iff
#print axioms actualOriginalPrimaryFamily_original_samples_of_inner_support
end GlobalEmbedding.Continuation
