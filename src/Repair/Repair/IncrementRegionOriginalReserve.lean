import Repair.IncrementRegionLiteralData

/-! Original signed noncritical and Sym² reserves on the actual buffered
interaction domain. The active domains and original transition bounds
supply every chart change. Proper labels are required only where the
actual primary cutoff supports meet. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance regionReserveRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance regionReserveSquareNormed {E : Type*}
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

theorem increment_actual_interaction_support_overlap
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (theta : Ep × M → ℝ) (radius buffer coordinateBound : ℝ)
    (geometry : RepairReferenceActualInteractionGeometry Data i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M)) theta radius buffer coordinateBound)
    (hNonempty : geometry.domain.Nonempty) :
    (tsupport (Data.cutoff r.val.1.1) ∩ tsupport (Data.cutoff r.val.1.2)).Nonempty := by
  let W : Set (Ep × M) := (Data.parameterChart i.2).target ×ˢ univ
  let pull : Ep × M → P × M := fun z => ((Data.parameterChart i.2).symm z.1,z.2)
  have hPull : ContinuousOn pull W :=
    ((Data.parameterChart i.2).symm.continuousOn.comp continuous_fst.continuousOn
      (fun z hz => hz.1)).prodMk continuous_snd.continuousOn
  have hRelative (nu : Fin Data.primaryCount) (z : Ep × M)
      (hz : z ∈ incrementsGlobalRelativeSupport W (fun w => Data.cutoff nu (pull w))) :
      pull z ∈ tsupport (Data.cutoff nu) := by
    obtain ⟨w,hw,rfl⟩ := hz
    exact tsupport_comp_subset_preimage _ (continuousOn_iff_continuous_restrict.mp hPull) hw
  obtain ⟨z,hz⟩ := geometry.carrier_nonempty hNonempty
  exact ⟨pull z,hRelative _ _ hz.2.1,hRelative _ _ hz.2.2⟩

theorem increment_actual_region_original_reserves
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (C : UniformActualGoodDictionaryCover K) (R T : ℝ) (hT : 0 < T) (labelBound : ℕ)
    (literal : IncrementActualLiteralPhaseData Data C R T labelBound)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (theta : Ep × M → ℝ) (radius buffer coordinateBound : ℝ)
    (geometry : RepairReferenceActualInteractionGeometry Data i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M)) theta radius buffer coordinateBound)
    (Parameter Spatial : ℕ → ℝ) (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (hSpatial : Spatial 1 ≤ T) (z : X) (hz : z ∈ geometry.domain) :
    (C.covectorRadius/2)/T ≤ ‖fderiv ℝ (fun x : D => actualOriginalParameterSignedPhase Data i r.val
      (z.1,(Data.atlas.chart i.1).symm x)) z.2‖ ∧
    ∀ v, (incrementUniformSignedMargin C R/T^2)*‖v‖ ≤ ‖covectorRestriction
      (round4ActualPhaseOperatorInChart (actualOriginalOpenParameterSlice Data i)
        (fun _ => Data.atlas.chart i.1) z)
      (fderiv ℝ (fun x : D => actualOriginalParameterSignedPhase Data i r.val
        (z.1,(Data.atlas.chart i.1).symm x)) z.2) v‖ := by
  let observer := Data.atlas.chart i.1
  let left := Data.atlas.chart (literal.owner r.val.1.1)
  let right := Data.atlas.chart (literal.owner r.val.1.2)
  let x := observer.symm z.2
  let p := (Data.parameterChart i.2).symm z.1
  let F := actualOriginalOpenParameterSlice Data i z.1
  let w := repairReferenceSignedHierarchy C R T
  let xi := (C.template (literal.index r.val.1.1)).covectors (literal.edge r.val.1.1)
  let eta := (C.template (literal.index r.val.1.2)).covectors (literal.edge r.val.1.2)
  let phase := incrementLiteralSignedPhase left right xi eta (w^literal.label r.val.1.1)
    (w^literal.label r.val.1.2) r.val.2
  have hAL := round3_prepared_native_primary_active Data i _ (geometry.active hz).1
  have hAR := round3_prepared_native_primary_active Data i _ (geometry.active hz).2
  have hxO : x ∈ observer.source := observer.map_target (geometry.target hz).2
  have hxL : x ∈ left.source := literal.source _ _ hAL.1
  have hxR : x ∈ right.source := literal.source _ _ hAR.1
  have hxEq : observer x=z.2 := observer.right_inv (geometry.target hz).2
  have hF : ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ F := actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1
  have hFeq : F = fun y => Data.F (p,y) := actualOriginalOpenParameterSlice_eq Data i z.1 hAL.2.1
  have hOpL : ‖repairReferenceSliceOperator F left (left x)‖ ≤ R ∧
      repairReferenceSliceOperator F left (left x) ∈ (C.template (literal.index r.val.1.1)).operatorDomain := by
    rw [hFeq]
    exact literal.operator r.val.1.1 (p,x) hAL.1
  have hOpR : ‖repairReferenceSliceOperator F right (right x)‖ ≤ R ∧
      repairReferenceSliceOperator F right (right x) ∈ (C.template (literal.index r.val.1.2)).operatorDomain := by
    rw [hFeq]
    exact literal.operator r.val.1.2 (p,x) hAR.1
  have hTrans (nu : Fin Data.primaryCount) (hnu : nu=r.val.1.1 ∨ nu=r.val.1.2)
      (k : Fin Data.atlas.count) (hxK : x ∈ (Data.atlas.chart k).source) :
      ‖fderiv ℝ (Data.atlas.chart k ∘ (Data.atlas.chart (literal.owner nu)).symm)
        (Data.atlas.chart (literal.owner nu) x)‖ ≤ T := by
    have ha : (p,x) ∈ Data.primaryDomain nu := by
      rcases hnu with rfl | rfl
      · exact hAL.1
      · exact hAR.1
    have hOwn := literal.source nu _ ha
    exact (increment_actual_spatial_transition_first Data hd Parameter Spatial transition
      (literal.owner nu) k (Data.atlas.chart (literal.owner nu) x)
      ((Data.atlas.chart (literal.owner nu)).map_source hOwn)
      (by simpa only [(Data.atlas.chart (literal.owner nu)).left_inv hOwn] using hxK)
      (literal.owner_samples nu _ ha)).trans hSpatial
  let Q (f : M → ℝ) : Prop :=
    (C.covectorRadius/2)/T ≤ ‖fderiv ℝ (f ∘ observer.symm) (observer x)‖ ∧
    ∀ v, (incrementUniformSignedMargin C R/T^2)*‖v‖ ≤
      ‖covectorRestriction (repairReferenceSliceOperator F observer (observer x))
        (fderiv ℝ (f ∘ observer.symm) (observer x)) v‖
  have hOut : Q phase := by
    by_cases heq : r.val.1.1=r.val.1.2
    · have hb : r.val.2=0 ∨ r.val.2=3 := r.property.resolve_left (not_not_intro heq)
      have hh := increment_literal_doubled_reserves C R T hT F hF observer right
        (hd.atlas_smooth.chart_mem _) (hd.atlas_smooth.chart_mem _) x hxO hxR
        (literal.index r.val.1.2) (literal.edge r.val.1.2) hOpR.1 hOpR.2
        (hTrans _ (Or.inr rfl) i.1 hxO) (literal.label r.val.1.2) r.val.2 hb
      simpa only [Q,phase,left,right,xi,eta,heq] using hh
    · exact increment_literal_signed_reserves C R T hT F hF observer left right
        (hd.atlas_smooth.chart_mem _) (hd.atlas_smooth.chart_mem _) (hd.atlas_smooth.chart_mem _)
        x hxO hxL hxR (literal.index r.val.1.1) (literal.index r.val.1.2)
        (literal.edge r.val.1.1) (literal.edge r.val.1.2) hOpL.1 hOpR.1 hOpL.2 hOpR.2
        (hTrans _ (Or.inl rfl) _ hxR) (hTrans _ (Or.inr rfl) _ hxL)
        (hTrans _ (Or.inl rfl) i.1 hxO) (hTrans _ (Or.inr rfl) i.1 hxO)
        (literal.label r.val.1.1) (literal.label r.val.1.2)
        (literal.proper _ _ heq (increment_actual_interaction_support_overlap Data i r theta radius buffer
          coordinateBound geometry ⟨z,hz⟩)) r.val.2
  have he : (fun y : M => actualOriginalParameterSignedPhase Data i r.val (z.1,y)) = phase := by
    funext y
    simp only [actualOriginalParameterSignedPhase,literal.phase_eq]
    rfl
  have hOriginal := (congrArg Q he).mpr hOut
  let At (y : D) : Prop :=
    (C.covectorRadius/2)/T ≤ ‖fderiv ℝ (fun t : D => actualOriginalParameterSignedPhase Data i r.val
      (z.1,observer.symm t)) y‖ ∧
    ∀ v, (incrementUniformSignedMargin C R/T^2)*‖v‖ ≤
      ‖covectorRestriction (repairReferenceSliceOperator F observer y)
        (fderiv ℝ (fun t : D => actualOriginalParameterSignedPhase Data i r.val (z.1,observer.symm t)) y) v‖
  have hAt : At z.2 := (congrArg At hxEq).mp hOriginal
  exact hAt

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_actual_interaction_support_overlap
#print axioms GlobalEmbedding.Continuation.increment_actual_region_original_reserves
