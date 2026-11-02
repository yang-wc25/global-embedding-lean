import Repair.ReferencePlateauInteractionBuffer
import Repair.IncrementActualSignedRegion
import Probes.Round3ParameterCrossNativeData

/-! The genuine secondary interaction region is manufactured from the same
actual primary plateaus and the original parent collar. Its common radius
is numerical. The domain retains both original primary domains, the
original sampling set, and the original atlas inner region. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)
private local instance interactionProductChart : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance interactionTargetChart : ChartedSpace (Ep × D) (Ep × D) := chartedSpaceSelf (Ep × D)
private local instance interactionProductManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod («I» := 𝓘(ℝ,Ep)) (I' := I) (n := ∞) P M

structure RepairReferenceActualInteractionGeometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (W : Set (Ep × M)) (theta : Ep × M → ℝ)
    (R buffer coordinateBound : ℝ) where
  domain : Set X
  center : X
  isOpen : IsOpen domain
  carrier_radius : (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) ''
    (tsupport theta ∩ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W) ⊆ closedBall center R
  carrier_buffer : ∀ z ∈ (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) ''
    (tsupport theta ∩ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W), ball z buffer ⊆ domain
  target : domain ⊆ (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).target
  parent : MapsTo (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm domain W
  active : domain ⊆ actualOriginalPrimaryNativeOpen Data r.val.1.1 i ∩ actualOriginalPrimaryNativeOpen Data r.val.1.2 i
  inner : ∀ z ∈ domain, (Data.atlas.chart i.1).symm z.2 ∈ Data.atlas.inner i.1
  samples : ∀ z ∈ domain, parameterTensorModelEquiv (m+1) d z ∈
    incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
      Data.parameterNormDomain Data.parameterSet i
  coordinates : ∀ z ∈ domain, ‖z‖ ≤ coordinateBound
  carrier_nonempty : domain.Nonempty → (tsupport theta ∩
    actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W).Nonempty

theorem repair_reference_actual_original_interaction_geometry
    (parentBuffer derivativeBound R centerBound : ℝ) (hParent : 0 < parentBuffer)
    (hDerivative : 0 ≤ derivativeBound)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (theta : Ep × M → ℝ)
    (hTheta : tsupport theta ⊆ (Data.parameterChart i.2).target ×ˢ (Data.atlas.chart i.1).source)
    (plateau : Fin Data.primaryCount → P × M → ℝ)
    (hPlateau : ∀ nu, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (plateau nu))
    (hPlateauSource : ∀ nu, tsupport (plateau nu) ⊆ Data.primaryDomain nu)
    (hPlateauOne : ∀ nu z, z ∈ tsupport (Data.cutoff nu) → plateau nu z=1)
    (U : Set X) (hU : IsOpen U) (hUOpen : U ⊆ actualOriginalNativeOpen Data i)
    (hInner : ∀ z ∈ U, (Data.atlas.chart i.1).symm z.2 ∈ Data.atlas.inner i.1)
    (hSamples : ∀ z ∈ U, parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i)
    (hFirst : ∀ nu z, z ∈ U →
      ‖fderiv ℝ (plateau nu ∘ ((Data.parameterChart i.2).prod (Data.atlas.chart i.1)).symm) z‖ ≤ derivativeBound)
    (hParentBuffer : ∀ z ∈ tsupport theta,
      ball ((actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) z) parentBuffer ⊆ U)
    (center : X) (hCenter : ‖center‖ ≤ centerBound)
    (hRadius : (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) '' tsupport theta ⊆ closedBall center R) :
    Nonempty (RepairReferenceActualInteractionGeometry Data i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M)) theta R
      (repairReferenceInteractionBuffer parentBuffer derivativeBound)
      (centerBound+R+repairReferenceInteractionBuffer parentBuffer derivativeBound)) := by
  let W : Set (Ep × M) := (Data.parameterChart i.2).target ×ˢ (univ : Set M)
  let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
  let joint := (Data.parameterChart i.2).prod (Data.atlas.chart i.1)
  let K := q '' (tsupport theta ∩ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W)
  let A := actualOriginalPrimaryNativeOpen Data r.val.1.1 i
  let B := actualOriginalPrimaryNativeOpen Data r.val.1.2 i
  let pull : Ep × M → P × M := fun z => ((Data.parameterChart i.2).symm z.1,z.2)
  have hPull : ContinuousOn pull W :=
    ((Data.parameterChart i.2).symm.continuousOn.comp continuous_fst.continuousOn
      (fun z hz => hz.1)).prodMk continuous_snd.continuousOn
  have hRelative (nu : Fin Data.primaryCount) (z : Ep × M)
      (hz : z ∈ incrementsGlobalRelativeSupport W (fun w => Data.cutoff nu (pull w))) :
      pull z ∈ tsupport (Data.cutoff nu) := by
    obtain ⟨w,hw,rfl⟩ := hz
    exact tsupport_comp_subset_preimage _ (continuousOn_iff_continuous_restrict.mp hPull) hw
  have hJoint (z : X) (hz : z ∈ U) : z ∈ joint.target := by
    have hh := (round3Parameter_originalNativeOpen_iff Data i z).mp (hUOpen hz)
    exact ⟨hh.2.1,hh.1⟩
  have hJointSmooth : joint ∈ IsManifold.maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hd.parameter_charts_smooth i.2) (hd.atlas_smooth.chart_mem i.1)
  have hSmooth (nu : Fin Data.primaryCount) : ContDiffOn ℝ ∞ (plateau nu ∘ joint.symm) U := by
    have hp : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,ℝ) ∞ (plateau nu) := by
      rw [modelWithCornersSelf_prod]
      exact hPlateau nu
    exact (hp.comp_contMDiffOn ((contMDiffOn_symm_of_mem_maximalAtlas hJointSmooth).mono hJoint)).contDiffOn
  have hOne (nu : Fin Data.primaryCount) (z : X)
      (hz : z ∈ K) (hWhich : nu=r.val.1.1 ∨ nu=r.val.1.2) : (plateau nu ∘ joint.symm) z=1 := by
    obtain ⟨y,hy,rfl⟩ := hz
    have hs := hTheta hy.1
    have hpair : pull y ∈ tsupport (Data.cutoff nu) := by
      rcases hWhich with rfl | rfl
      · exact hRelative _ _ hy.2.1
      · exact hRelative _ _ hy.2.2
    change plateau nu ((Data.parameterChart i.2).symm y.1,
      (Data.atlas.chart i.1).symm (Data.atlas.chart i.1 y.2))=1
    rw [(Data.atlas.chart i.1).left_inv hs.2]
    exact hPlateauOne nu (pull y) hpair
  have hDomain (nu : Fin Data.primaryCount) (z : X) (hz : z ∈ U)
      (hnz : (plateau nu ∘ joint.symm) z ≠ 0) : z ∈ actualOriginalPrimaryNativeOpen Data nu i := by
    have ho := (round3Parameter_originalNativeOpen_iff Data i z).mp (hUOpen hz)
    apply round3_prepared_native_primary_mem Data i nu z ho.1 ho.2.1
    exact ⟨hPlateauSource nu (subset_tsupport _ hnz),ho.2.2,mem_univ _⟩
  have hBuffer (z : X) (hz : z ∈ K) : ball z parentBuffer ⊆ U := by
    obtain ⟨y,hy,rfl⟩ := hz
    exact hParentBuffer y hy.1
  have hBounded : K ⊆ closedBall center R := by
    rintro z ⟨y,hy,rfl⟩
    exact hRadius ⟨y,hy.1,rfl⟩
  have hGeom := repair_reference_actual_buffered_interaction parentBuffer derivativeBound hParent hDerivative
    U K A B hU (plateau r.val.1.1 ∘ joint.symm) (plateau r.val.1.2 ∘ joint.symm)
    (hSmooth _) (hSmooth _) (hFirst _) (hFirst _)
    (fun z hz => hOne _ z hz (Or.inl rfl)) (fun z hz => hOne _ z hz (Or.inr rfl))
    (hDomain _) (hDomain _) hBuffer center R hBounded
  let radius := repairReferenceInteractionBuffer parentBuffer derivativeBound
  let O := repairReferenceBufferedInteractionDomain K radius
  refine ⟨{ domain := O
            center := center
            isOpen := hGeom.2.1
            carrier_radius := hBounded
            carrier_buffer := hGeom.2.2.1
            target := ?_
            parent := ?_
            active := fun z hz => (hGeom.2.2.2.1 hz).2
            inner := fun z hz => hInner z (hGeom.2.2.2.1 hz).1
            samples := fun z hz => hSamples z (hGeom.2.2.2.1 hz).1
            coordinates := ?_
            carrier_nonempty := ?_ }⟩
  · intro z hz
    exact ⟨mem_univ _,((round3Parameter_originalNativeOpen_iff Data i z).mp
      (hUOpen (hGeom.2.2.2.1 hz).1)).1⟩
  · intro z hz
    exact ⟨((round3Parameter_originalNativeOpen_iff Data i z).mp
      (hUOpen (hGeom.2.2.2.1 hz).1)).2.1,mem_univ _⟩
  · intro z hz
    exact (hGeom.2.2.2.2.2.2 z hz).trans (by linarith)
  · intro ho
    obtain ⟨z,hz⟩ := (repair_reference_buffered_interaction_nonempty K radius hGeom.1).mp ho
    obtain ⟨y,hy,_⟩ := hz
    exact ⟨y,hy⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_actual_original_interaction_geometry
