import Repair.ReferenceSpatialPrimaryNative
import Repair.ReferenceSingletonPrimarySupply

/-! The actual single-piece primary packet, made from real global spatial
linear equivalences and actual original observing domains. No adapted chart,
final output estimate, or conditional ideal step is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

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

structure RepairReferenceSpatialPrimarySupply
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (owner : Fin Data.primaryCount → OpenPartialHomeomorph M D)
    (xi : Fin Data.primaryCount → D →L[ℝ] ℝ)
    (plateau : Fin Data.primaryCount → P × M → ℝ)
    (U : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X)
    (mu bound : ℝ) where
  spatial : Fin Data.primaryCount → D ≃L[ℝ] D
  spatial_phase : ∀ nu x, spatial nu x 0=xi nu x
  spatial_inverse_phase : ∀ nu y, xi nu ((spatial nu).symm y)=y 0
  spatial_bound : ∀ nu, ‖(spatial nu : D →L[ℝ] D)‖ ≤ 2*(1+2*bound)
  spatial_inverse_bound : ∀ nu, ‖((spatial nu).symm : D →L[ℝ] D)‖ ≤ 2*actualPhaseInverseConstant mu (2*bound)
  packet : Round3ParameterWholePrimaryPieceSupply Data theta
  card : ∀ nu i, (packet.s nu i).card=1
  source : ∀ nu i a z, z ∈ (packet.piece nu i a).native.source ↔ z ∈ U i ∧
    ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈ Data.primaryDomain nu
  forward : ∀ nu i a z, (packet.piece nu i a).native z=
    (z.1,spatial nu (owner nu ((Data.atlas.chart i.1).symm z.2)))
  inverse : ∀ nu i a z, (packet.piece nu i a).native.symm z=
    (z.1,Data.atlas.chart i.1 ((owner nu).symm ((spatial nu).symm z.2)))
  cutoff : ∀ nu i a, round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (packet.piece nu i a)=
    fun z => theta i z*plateau nu z

theorem repair_reference_actual_spatial_primary_supply
    (mu bound T : ℝ) (hmu : 0 < mu) (hBound : 0 ≤ bound) (hT : 0 < T)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hThetaSource : ∀ i, tsupport (theta i) ⊆
      (Data.parameterChart i.2).source ×ˢ (Data.atlas.chart i.1).source)
    (owner : Fin Data.primaryCount → OpenPartialHomeomorph M D)
    (hOwner : ∀ nu, owner nu ∈ IsManifold.maximalAtlas I ∞ M)
    (xi : Fin Data.primaryCount → D →L[ℝ] ℝ)
    (hXiLower : ∀ nu, mu ≤ ‖xi nu‖) (hXiUpper : ∀ nu, ‖xi nu‖ ≤ bound)
    (hPhase : ∀ nu z, Data.phase nu z=xi nu (owner nu z.2))
    (hOwnerSource : ∀ nu z, z ∈ Data.primaryDomain nu → z.2 ∈ (owner nu).source)
    (plateau : Fin Data.primaryCount → P × M → ℝ)
    (hPlateau : ∀ nu, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (plateau nu))
    (hPlateauSource : ∀ nu, tsupport (plateau nu) ⊆ Data.primaryDomain nu)
    (hGerm : ∀ nu z, z ∈ tsupport (Data.cutoff nu) → plateau nu =ᶠ[𝓝 z] fun _ => 1)
    (U : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X)
    (hU : ∀ i, IsOpen (U i)) (hUOpen : ∀ i, U i ⊆ actualOriginalNativeOpen Data i)
    (hUCover : ∀ i z, z ∈ tsupport (theta i) →
      (Data.parameterChart i.2 z.1,Data.atlas.chart i.1 z.2) ∈ U i)
    (hTransition : ∀ nu i z, z ∈ U i →
      ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈ Data.primaryDomain nu →
      z ∈ (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)).source →
      ‖fderiv ℝ (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)) z‖ ≤ T) :
    Nonempty (RepairReferenceSpatialPrimarySupply Data theta owner xi plateau U mu bound) := by
  choose L hL hLi hLn hLin using fun nu =>
    repair_reference_spatial_linear_phase mu bound hmu hBound (xi nu) (hXiLower nu) (hXiUpper nu)
  have hB : 1 ≤ 2*(1+2*bound) := by linarith
  choose native slices hData hSource hParam hActive hFirst hForward hInverse using fun nu i =>
    repair_reference_spatial_primary_native Data hd nu i (owner nu) (hOwner nu) (xi nu)
      (L nu) (hL nu) (hPhase nu) (hOwnerSource nu) (U i) (hU i) (hUOpen i)
      (2*(1+2*bound)) T hB hT (hLn nu) (hTransition nu i)
  have hNative (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      (native nu i).source ⊆ actualOriginalNativeOpen Data i :=
    fun z hz => hUOpen i ((hSource nu i z).mp hz).1
  have hCover (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
      (z : P × M) (hz : z ∈ tsupport (theta i) ∩ tsupport (plateau nu)) :
      (Data.parameterChart i.2 z.1,z.2) ∈
        (actualHostAdaptedChart (Data.atlas.chart i.1) (native nu i)).source := by
    have hzs := hThetaSource i hz.1
    refine ⟨⟨mem_univ _,hzs.2⟩,?_⟩
    change (Data.parameterChart i.2 z.1,Data.atlas.chart i.1 z.2) ∈ (native nu i).source
    apply (hSource nu i _).mpr
    refine ⟨hUCover i z hz.1,?_⟩
    simpa only [(Data.parameterChart i.2).left_inv hzs.1,
      (Data.atlas.chart i.1).left_inv hzs.2] using hPlateauSource nu hz.2
  obtain ⟨packet,hCard,hNativeEq,hSlicesEq,hCutoff⟩ := repair_reference_singleton_primary_supply
    Data hd theta hCompact hSmooth (fun i z hz => ⟨(hThetaSource i hz).1,mem_univ _⟩)
    plateau hPlateau hGerm native slices hData hNative hParam hActive hCover
    ((2*(1+2*bound))*T) (mul_pos (zero_lt_one.trans_le hB) hT) hFirst
  refine ⟨{ spatial := L
            spatial_phase := hL
            spatial_inverse_phase := hLi
            spatial_bound := hLn
            spatial_inverse_bound := hLin
            packet := packet
            card := hCard
            source := ?_
            forward := ?_
            inverse := ?_
            cutoff := hCutoff }⟩
  · intro nu i a z
    rw [hNativeEq]
    exact hSource nu i z
  · intro nu i a z
    rw [hNativeEq]
    exact hForward nu i z
  · intro nu i a z
    rw [hNativeEq]
    exact hInverse nu i z

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_actual_spatial_primary_supply
