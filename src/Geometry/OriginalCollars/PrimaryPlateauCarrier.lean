import Repair.ReferenceOriginalInteractionGeometry
import Probes.ActualRelativeInteractionCarrier

/-!
# An actual primary construction carrier from its original plateau

The original plateau is one on the true primary cutoff support. Its
original joint first-derivative bound and the parent buffer therefore
produce an open primary construction carrier with a common radius.

The construction carrier is required to lie in the original primary and
parameter-open domains. It is not required to lie in the compact parameter
evaluation set. That extra requirement in the older interaction record
was unused by the geometric argument and fails for compact sets with
boundary. This module neither changes nor enlarges any norm domain.

Source: main.tex 591 (buffers and transition bounds), 698 (same actual
covering bumps and fixed refinements). The numerical radius is the
already-proved repairReferenceInteractionBuffer, not a new compact minimum.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.OriginalCollars

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M]
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
private local instance primaryPlateauProductChart : ChartedSpace (Ep × D) (P × M) :=
  prodChartedSpace Ep P D M
private local instance primaryPlateauTargetChart : ChartedSpace (Ep × D) (Ep × D) :=
  chartedSpaceSelf (Ep × D)
private local instance primaryPlateauProductManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod («I» := 𝓘(ℝ,Ep)) (I' := I) (n := ∞) P M

/-- Literal original support carrier in one original observing chart. -/
def originalNativePrimaryCarrier
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (nu : Fin Data.primaryCount) (theta : Ep × M → ℝ) : Set X :=
  (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) ''
    (tsupport theta ∩ incrementsGlobalRelativeSupport
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
      (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)))

theorem originalNativePrimaryCarrier_isCompact
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (nu : Fin Data.primaryCount) (theta : Ep × M → ℝ)
    (hCompact : IsCompact (tsupport theta))
    (hTheta : tsupport theta ⊆
      (Data.parameterChart i.2).target ×ˢ (Data.atlas.chart i.1).source) :
    IsCompact (originalNativePrimaryCarrier Data i nu theta) := by
  let W : Set (Ep × M) := (Data.parameterChart i.2).target ×ˢ (univ : Set M)
  let f := fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)
  have hCarrier : IsCompact (tsupport theta ∩ incrementsGlobalRelativeSupport W f) := by
    dsimp only [incrementsGlobalRelativeSupport]
    simpa only [inter_self] using actual_compact_interaction_carrier
      (tsupport theta) W hCompact (fun z hz => ⟨(hTheta hz).1,mem_univ _⟩) f f
  apply hCarrier.image_of_continuousOn
  apply (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).continuousOn.mono
  exact fun z hz => ⟨mem_univ _, (hTheta hz.1).2⟩

/-- Produce the actual open primary construction domain. No original
evaluation-set inclusion is imposed on that open construction domain. -/
theorem original_primary_buffer_from_actual_plateau
    (parentBuffer derivativeBound R : ℝ) (hParent : 0 < parentBuffer)
    (hDerivative : 0 ≤ derivativeBound)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (theta : Ep × M → ℝ) (hCompact : IsCompact (tsupport theta))
    (hTheta : tsupport theta ⊆
      (Data.parameterChart i.2).target ×ˢ (Data.atlas.chart i.1).source)
    (plateau : P × M → ℝ) (hPlateau : ContMDiff IJ 𝓘(ℝ,ℝ) ∞ plateau)
    (hPlateauSource : tsupport plateau ⊆ Data.primaryDomain nu)
    (hPlateauOne : ∀ z ∈ tsupport (Data.cutoff nu), plateau z=1)
    (U : Set X) (hU : IsOpen U) (hUOpen : U ⊆ actualOriginalNativeOpen Data i)
    (hFirst : ∀ z ∈ U,
      ‖fderiv ℝ (plateau ∘ ((Data.parameterChart i.2).prod (Data.atlas.chart i.1)).symm) z‖ ≤
        derivativeBound)
    (hParentBuffer : ∀ z ∈ tsupport theta,
      ball ((actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) z) parentBuffer ⊆ U)
    (center : X)
    (hRadius : (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) ''
      tsupport theta ⊆ closedBall center R) :
    let radius := repairReferenceInteractionBuffer parentBuffer derivativeBound
    let K := originalNativePrimaryCarrier Data i nu theta
    ∃ O : Set X,
      0 < radius ∧ IsCompact K ∧ IsOpen O ∧ K ⊆ closedBall center R ∧
      (∀ z ∈ K, ball z radius ⊆ O) ∧
      O ⊆ U ∩ actualOriginalPrimaryNativeOpen Data nu i ∧
      O ⊆ (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).target ∧
      MapsTo (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm O
        ((Data.parameterChart i.2).target ×ˢ (univ : Set M)) ∧
      O ⊆ ball center (R+radius) ∧ (O.Nonempty ↔ K.Nonempty) := by
  intro radius K
  let W : Set (Ep × M) := (Data.parameterChart i.2).target ×ˢ (univ : Set M)
  let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
  let joint := (Data.parameterChart i.2).prod (Data.atlas.chart i.1)
  let A := actualOriginalPrimaryNativeOpen Data nu i
  let pull : Ep × M → P × M := fun z => ((Data.parameterChart i.2).symm z.1,z.2)
  have hPull : ContinuousOn pull W :=
    ((Data.parameterChart i.2).symm.continuousOn.comp continuous_fst.continuousOn
      (fun z hz => hz.1)).prodMk continuous_snd.continuousOn
  have hRelative (z : Ep × M)
      (hz : z ∈ incrementsGlobalRelativeSupport W (fun w => Data.cutoff nu (pull w))) :
      pull z ∈ tsupport (Data.cutoff nu) := by
    obtain ⟨w,hw,rfl⟩ := hz
    exact tsupport_comp_subset_preimage _ (continuousOn_iff_continuous_restrict.mp hPull) hw
  have hJoint (z : X) (hz : z ∈ U) : z ∈ joint.target := by
    have hh := (round3Parameter_originalNativeOpen_iff Data i z).mp (hUOpen hz)
    exact ⟨hh.2.1,hh.1⟩
  have hJointSmooth : joint ∈ IsManifold.maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod
      (hd.parameter_charts_smooth i.2) (hd.atlas_smooth.chart_mem i.1)
  have hSmooth : ContDiffOn ℝ ∞ (plateau ∘ joint.symm) U := by
    have hp : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,ℝ) ∞ plateau := by
      rw [modelWithCornersSelf_prod]
      exact hPlateau
    exact (hp.comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas hJointSmooth).mono hJoint)).contDiffOn
  have hOne (z : X) (hz : z ∈ K) : (plateau ∘ joint.symm) z=1 := by
    obtain ⟨y,hy,rfl⟩ := hz
    change plateau ((Data.parameterChart i.2).symm y.1,
      (Data.atlas.chart i.1).symm (Data.atlas.chart i.1 y.2))=1
    rw [(Data.atlas.chart i.1).left_inv (hTheta hy.1).2]
    exact hPlateauOne (pull y) (hRelative y hy.2)
  have hDomain (z : X) (hz : z ∈ U)
      (hnz : (plateau ∘ joint.symm) z ≠ 0) : z ∈ A := by
    have ho := (round3Parameter_originalNativeOpen_iff Data i z).mp (hUOpen hz)
    apply round3_prepared_native_primary_mem Data i nu z ho.1 ho.2.1
    exact ⟨hPlateauSource (subset_tsupport _ hnz),ho.2.2,mem_univ _⟩
  have hBuffer (z : X) (hz : z ∈ K) : ball z parentBuffer ⊆ U := by
    obtain ⟨y,hy,rfl⟩ := hz
    exact hParentBuffer y hy.1
  have hBounded : K ⊆ closedBall center R := by
    rintro z ⟨y,hy,rfl⟩
    exact hRadius ⟨y,hy.1,rfl⟩
  have hGeom := repair_reference_actual_buffered_interaction
    parentBuffer derivativeBound hParent hDerivative U K A A hU
    (plateau ∘ joint.symm) (plateau ∘ joint.symm) hSmooth hSmooth hFirst hFirst
    hOne hOne hDomain hDomain hBuffer center R hBounded
  let O := repairReferenceBufferedInteractionDomain K radius
  refine ⟨O, hGeom.1, originalNativePrimaryCarrier_isCompact Data i nu theta hCompact hTheta,
    hGeom.2.1, hBounded, hGeom.2.2.1,
    (fun z hz => ⟨(hGeom.2.2.2.1 hz).1,(hGeom.2.2.2.1 hz).2.1⟩), ?_, ?_,
    hGeom.2.2.2.2.1, repair_reference_buffered_interaction_nonempty K radius hGeom.1⟩
  · intro z hz
    exact ⟨mem_univ _,((round3Parameter_originalNativeOpen_iff Data i z).mp
      (hUOpen (hGeom.2.2.2.1 hz).1)).1⟩
  · intro z hz
    exact ⟨((round3Parameter_originalNativeOpen_iff Data i z).mp
      (hUOpen (hGeom.2.2.2.1 hz).1)).2.1,mem_univ _⟩

end GlobalEmbedding.Continuation.OriginalCollars

#print axioms GlobalEmbedding.Continuation.OriginalCollars.originalNativePrimaryCarrier_isCompact
#print axioms GlobalEmbedding.Continuation.OriginalCollars.original_primary_buffer_from_actual_plateau
