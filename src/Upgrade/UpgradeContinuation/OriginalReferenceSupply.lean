import UpgradeContinuation.ReferenceAllowedClass
import UpgradeContinuation.ReferenceBundle
import Probes.Round3PreparedReferencePrimaryPacket

/-!
# The actual reference seed, primary packet, and fixed smoothing supply

This packages one choice of the existing native factory, its actual prepared
primary family, and its fixed smoothing packet.  The reference map is exactly
the original input map at every zero-dimensional parameter.  A later passive
probe construction can keep this one supply unchanged throughout all its
secondary and repair stages.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold Bundle Metric GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical

namespace GlobalEmbedding.Continuation.UpgradeContinuation

variable {m N : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => ZeroParameter
local notation "X" => Z × D
local notation "IM" => 𝓘(ℝ,D)

/-- One manufactured original reference supply.  The fields are actual
factory outputs, with no completed probe or same-Q conclusion stored. -/
structure OriginalReferenceSupply (F : M → V) where
  fixedClass : ClosureNovFixedClass m 0 N M Z
  allowed : fixedClass.AllowedMap (fun z : Z × M => F z.2)
  source_compact : ∀ i, IsCompact (allowed.data.atlas.support i)
  source_cover : ∀ x, ∃ i, x ∈ allowed.data.atlas.support i
  baseIndex : Fin allowed.data.atlas.count × Fin allowed.data.parameterCount
  parameter_identity : allowed.data.parameterChart baseIndex.2 = OpenPartialHomeomorph.refl Z
  subdivisions : Fin allowed.data.primaryCount → Fin allowed.data.atlas.count → Finset X
  primary : Round3PreparedReferencePrimaryPacket allowed.data allowed.domain allowed.nativeSmooth
    allowed.native_properties.2.1 baseIndex
    (Sigma (fun nu : Fin allowed.data.primaryCount =>
      Sigma (fun host : Fin allowed.data.atlas.count => ↥(subdivisions nu host))))
    ((fixedClass.geometry.Ds+1)*5^Module.finrank ℝ X)

#print axioms OriginalReferenceSupply
#print axioms ClosureNovFixedClass.AllowedMap.data
#print axioms ClosureNovFixedClass.AllowedMap.baseSmoothing

namespace OriginalReferenceSupply
variable {F : M → EuclideanSpace ℝ (Fin N)} (s : OriginalReferenceSupply (m := m) (N := N) F)
include N

abbrev seed : IncrementsOriginalNativeData (m+1) 0 N M Z := s.allowed.data
abbrev domain : IncrementsOriginalDomainConditions s.seed := s.allowed.domain
abbrev smooth : IncrementsOriginalSmoothInputs s.seed := s.allowed.nativeSmooth
abbrev phase : IncrementsOriginalPhaseConditions s.seed s.domain s.smooth :=
  s.allowed.native_properties.1
abbrev freeNormal : IncrementsOriginalFreeNormalConditions s.seed s.domain s.smooth :=
  s.allowed.native_properties.2.1
abbrev immersion : IncrementsOriginalSliceImmersionInputs s.seed := s.allowed.immersion
abbrev ellipticity : IncrementsOriginalCoordinateEllipticityInputs s.seed s.fixedClass.lower :=
  s.allowed.ellipticity_inputs
abbrev linearSmooth : IncrementsOriginalLinearSmoothInputs s.seed := s.allowed.native_properties.2.2.2.2.1
abbrev decomposition : IncrementsOriginalQualitativeDecompositionInputs s.seed :=
  s.allowed.native_properties.2.2.1
abbrev reserve : IncrementsOriginalDecompositionReserveInputs s.seed s.fixedClass.numerical.reserve :=
  s.allowed.native_properties.2.2.2.1
abbrev fixed : Round3RepairFixedSmoothingPacket s.seed
    s.fixedClass.numerical.BS s.fixedClass.numerical.TS
    s.fixedClass.numerical.BP s.fixedClass.numerical.TP
    s.fixedClass.numerical.Ds s.fixedClass.numerical.Dp
    s.fixedClass.numerical.smoothingRadius s.fixedClass.numerical.smoothingRadius_pos
    (repairOriginalActualReferenceProfile s.seed) (repairOriginalActualGivenProfile s.seed) :=
  s.allowed.baseSmoothing
abbrev subdivisionIndex : Type := Sigma (fun nu : Fin s.seed.primaryCount =>
  Sigma (fun host : Fin s.seed.atlas.count => ↥(s.subdivisions nu host)))
abbrev refinementMultiplicity : ℕ := (s.fixedClass.geometry.Ds+1)*5^Module.finrank ℝ X

theorem map_eq : s.seed.F = fun z : Z × M => F z.2 := rfl
theorem parameterSet_eq : s.seed.parameterSet = univ := rfl
theorem fixed_reference_eq : s.seed.F = s.fixed.referenceMap := rfl
theorem fixed_source_domain_eq : s.seed.sourceNormDomain = s.fixed.Omega := rfl
theorem fixed_parameter_domain_eq : s.seed.parameterNormDomain = s.fixed.Q := rfl

end OriginalReferenceSupply

/-- Original qualitative immersion and phase regularity manufacture one
complete reference supply, including the genuine primary packet. -/
theorem exists_originalReference_supply [Nonempty M]
    (hdim : 2 ≤ m+1) (hambient : (m+1)*(m+2)/2 < N)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hphase : PhaseRegular F hF) : Nonempty (OriginalReferenceSupply (m := m) F) := by
  obtain ⟨c,h,hparameter,hQ,hcompact,hcover⟩ :=
    exists_originalReference_allowedClass hdim hambient F hF himm hphase
  obtain ⟨i,hi⟩ := c.geometry.source.cover (Classical.choice (inferInstance : Nonempty M))
  obtain ⟨ip,hip⟩ := c.geometry.parameter.cover (0 : Z)
  let base : Fin h.data.atlas.count × Fin h.data.parameterCount := (i,ip)
  have hId : h.data.parameterChart base.2 = OpenPartialHomeomorph.refl Z := hparameter ip
  have hbound : ∀ j, (h.data.atlas.chart j) '' h.data.atlas.inner j ⊆
      closedBall (0 : D) c.geometry.coordinateRadius := by
    intro j y hy
    obtain ⟨x,hx,rfl⟩ := hy
    have hs := c.geometry.source_sampling j
      (bufferedInner_subset_sampling c.geometry.source j
        (bufferedInnerCoordinates_mem c.geometry.source j hx))
    change c.geometry.source.chart j x ∈ closedBall (0 : D) c.geometry.coordinateRadius
    simpa only [mem_closedBall,dist_zero_right] using c.geometry.source_bound j _ hs
  obtain ⟨subdivisions,⟨primary⟩⟩ := round3_actual_reference_primary_packet
    h.data h.domain h.nativeSmooth h.native_properties.1 h.native_properties.2.1
    h.immersion base hId c.geometry.BS c.geometry.TS c.geometry.BS_nonneg c.geometry.TS_nonneg
    c.geometry.Ds c.geometry.sourcePreparation (fun _ => 0) c.geometry.coordinateRadius hbound
  exact ⟨{
    fixedClass := c
    allowed := h
    source_compact := hcompact
    source_cover := hcover
    baseIndex := base
    parameter_identity := hId
    subdivisions := subdivisions
    primary := primary }⟩

omit [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)] in
/-- The auxiliary tangent norms are chosen internally. -/
def OriginalReferenceSupplyFromMap (F : M → V) : Type _ :=
  letI := referenceRiemannianBundle (n := m+1) (M := M)
  OriginalReferenceSupply (m := m) F

omit [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)] in
/-- No auxiliary metric or norm certificate occurs in this original-map
entrance.  Every constant and packet is fixed before a probe scale is used. -/
theorem exists_originalReference_supply_from_map [Nonempty M]
    (hdim : 2 ≤ m+1) (hambient : (m+1)*(m+2)/2 < N)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hphase : PhaseRegular F hF) : Nonempty (OriginalReferenceSupplyFromMap (m := m) F) := by
  letI := referenceRiemannianBundle (n := m+1) (M := M)
  exact exists_originalReference_supply (m := m) hdim hambient F hF himm hphase

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.OriginalReferenceSupply.fixed
#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.exists_originalReference_supply
#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.exists_originalReference_supply_from_map
