import Repair.ReferenceSpatialLinearPhase
import Repair.ReferenceRehostedChart
import Probes.Round3ParameterCrossNativeData

/-! Actual primary charts in every observing source/parameter chart.
The spatial linear equivalence is fixed once. Parameter coordinates are
unchanged; the original physical primary carrier supplies the domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric
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

theorem repair_reference_spatial_primary_native
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (owner : OpenPartialHomeomorph M D)
    (hOwner : owner ∈ IsManifold.maximalAtlas I ∞ M)
    (xi : D →L[ℝ] ℝ) (L : D ≃L[ℝ] D) (hL : ∀ x, L x 0=xi x)
    (hPhase : ∀ z, Data.phase nu z=xi (owner z.2))
    (hOwnerSource : ∀ z ∈ Data.primaryDomain nu, z.2 ∈ owner.source)
    (U : Set X) (hU : IsOpen U) (hUOpen : U ⊆ actualOriginalNativeOpen Data i)
    (B T : ℝ) (hB : 1 ≤ B) (hT : 0 < T) (hLNorm : ‖(L : D →L[ℝ] D)‖ ≤ B)
    (hTransition : ∀ z ∈ U,
      ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈ Data.primaryDomain nu →
      z ∈ (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) owner).source →
      ‖fderiv ℝ (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) owner) z‖ ≤ T) :
    ∃ (native : OpenPartialHomeomorph X X) (slices : Ep → OpenPartialHomeomorph M D),
      ActualOriginalHostSliceData (Data.atlas.chart i.1) native
        (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) slices ∧
      (∀ z, z ∈ native.source ↔ z ∈ U ∧
        ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈ Data.primaryDomain nu) ∧
      ((actualHostAdaptedChart (Data.atlas.chart i.1) native).source ⊆
        (Data.parameterChart i.2).target ×ˢ (univ : Set M)) ∧
      (∀ z ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) native).source,
        ((Data.parameterChart i.2).symm z.1,z.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) ∧
      (∀ z ∈ native.source, ‖fderiv ℝ native z‖ ≤ B*T) ∧
      (∀ z, native z=(z.1,L (owner ((Data.atlas.chart i.1).symm z.2)))) ∧
      (∀ z, native.symm z=(z.1,Data.atlas.chart i.1 (owner.symm (L.symm z.2)))) := by
  let observer := Data.atlas.chart i.1
  let joint := (Data.parameterChart i.2).prod observer
  let transition := repairReferenceHostTransition («Ep» := Ep) observer owner
  let linear := (ContinuousLinearEquiv.refl ℝ Ep).prodCongr L
  let V : Set X := U ∩ (joint.target ∩ joint.symm ⁻¹' Data.primaryDomain nu)
  have hV : IsOpen V := hU.inter (joint.symm.isOpen_inter_preimage (hd.primary_open nu))
  let native := ((transition.trans linear.toHomeomorph.toOpenPartialHomeomorph).restrOpen V hV)
  have hSource (z : X) : z ∈ native.source ↔ z ∈ U ∧ joint.symm z ∈ Data.primaryDomain nu := by
    constructor
    · intro hz
      exact ⟨hz.2.1,hz.2.2.2⟩
    · rintro ⟨hzU,hzP⟩
      have ho := (round3Parameter_originalNativeOpen_iff Data i z).mp (hUOpen hzU)
      have ht : z ∈ transition.source := ⟨mem_univ _,ho.1,hOwnerSource _ hzP⟩
      exact ⟨⟨ht,mem_univ _⟩,hzU,⟨ho.2.1,ho.1⟩,hzP⟩
  have hSourceTransition (z : X) (hz : z ∈ native.source) : z ∈ transition.source := hz.1.1
  have ht := repair_reference_host_transition_smooth («Ep» := Ep) observer owner
    (hd.atlas_smooth.chart_mem i.1) hOwner
  have hn : ContDiffOn ℝ ∞ native native.source :=
    linear.contDiff.comp_contDiffOn (ht.1.mono (fun z hz => hSourceTransition z hz))
  have hni : ContDiffOn ℝ ∞ native.symm native.target :=
    ht.2.comp linear.symm.contDiff.contDiffOn (fun z hz => hz.1.2)
  have hTarget (z : X) (hz : z ∈ native.source) :
      z ∈ (actualOriginalHostJointChart («Ep» := Ep) observer).target :=
    ⟨mem_univ _,(hSourceTransition z hz).2.1⟩
  have hParameter (z : X) (hz : z ∈ native.source) : (native z).1=z.1 := rfl
  have hNativePhase (z : X) (hz : z ∈ native.source) :
      (native z).2 0=Data.phase nu ((Data.parameterChart i.2).symm z.1,observer.symm z.2) := by
    rw [hPhase]
    exact hL _
  obtain ⟨hat,ha,hai,hforw,slices,he⟩ := actual_adapted_chart_original_host observer
    (hd.atlas_smooth.chart_mem i.1)
    (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2))
    native hTarget hn hni hParameter hNativePhase
  have hPhysical (z : Ep × M)
      (hz : z ∈ (actualHostAdaptedChart observer native).source) :
      (z.1,observer z.2) ∈ native.source := hz.2
  have hOriginal (z : Ep × M)
      (hz : z ∈ (actualHostAdaptedChart observer native).source) :
      z.2 ∈ observer.source := hz.1.2
  have hLinear : ‖(linear : X →L[ℝ] X)‖ ≤ B := by
    apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hB)
    intro z
    change ‖(z.1,L z.2)‖ ≤ B*‖z‖
    rw [Prod.norm_def]
    apply max_le
    · exact (norm_fst_le z).trans (by nlinarith [norm_nonneg z])
    · exact (L.toContinuousLinearMap.le_of_opNorm_le hLNorm z.2).trans
        (mul_le_mul_of_nonneg_left (norm_snd_le z) (zero_le_one.trans hB))
  refine ⟨native,slices,⟨hat,ha,hai,hforw,he⟩,hSource,?_,?_,?_,fun _ => rfl,fun _ => rfl⟩
  · intro z hz
    have hu := (hSource _).mp (hPhysical z hz)
    exact ⟨((round3Parameter_originalNativeOpen_iff Data i _).mp (hUOpen hu.1)).2.1,mem_univ _⟩
  · intro z hz
    have hu := (hSource _).mp (hPhysical z hz)
    have ho := (round3Parameter_originalNativeOpen_iff Data i _).mp (hUOpen hu.1)
    have hp := hu.2
    change ((Data.parameterChart i.2).symm z.1,observer.symm (observer z.2)) ∈ Data.primaryDomain nu at hp
    constructor
    · simpa only [observer.left_inv (hOriginal z hz)] using hp
    · exact ⟨ho.2.2,mem_univ _⟩
  · intro z hz
    have hts := hSourceTransition z hz
    have htd := (ht.1.contDiffAt (transition.open_source.mem_nhds hts)).differentiableAt (by simp)
    change ‖fderiv ℝ (linear ∘ transition) z‖ ≤ _
    rw [fderiv_comp z linear.differentiableAt htd,ContinuousLinearEquiv.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hLinear (hTransition z ((hSource z).mp hz).1 ((hSource z).mp hz).2 hts)
        (norm_nonneg _) (zero_le_one.trans hB))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_spatial_primary_native
