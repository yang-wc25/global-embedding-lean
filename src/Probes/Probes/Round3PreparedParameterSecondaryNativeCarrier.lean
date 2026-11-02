import Probes.Round3PreparedParameterSecondaryTransport
import Probes.Round3ParameterNativeEtaSmooth

/-! Canonical native secondary cutoffs are smooth on the actual observer
parameter domain. Their effective relative support is exactly the inverse
image of the physical carrier there; no off-chart smoothness is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Set Function Manifold IsManifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

theorem round3_prepared_native_tsupport_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : OpenPartialHomeomorph X Y) (f : X → ℝ) (y : Y) (hy : y ∈ q.target) :
    y ∈ tsupport (fun z => f (q.symm z)) ↔ q.symm y ∈ tsupport f := by
  constructor
  · intro hs
    by_contra hn
    have he := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
      (q.symm.continuousOn.continuousAt (q.open_target.mem_nhds hy))
    exact (notMem_tsupport_iff_eventuallyEq.mpr he) hs
  · intro hs
    have hh := round3Parameter_native_tsupport q f (q.symm y) (q.map_target hy) hs
    simpa only [q.right_inv hy] using hh

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

 theorem round3_prepared_parameter_secondary_native_carrier
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (host : Fin Data.atlas.count) (ip : Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (choice : Round3ParameterSecondaryChoice P M m)
    (hPreserves : Round3ParameterChartPreserves choice.chart)
    (hSource : round3PreparedParameterSecondaryCarrier Data r choice ⊆ choice.chart.source) :
    let B := Data.parameterChart ip
    let W := B.target ×ˢ (univ : Set M)
    let native := (choice.pullback B).toNative
    let carrier := tsupport native.cutoff ∩ actualOriginalParameterSupportPair Data
      (host,ip) r.val.1.1 r.val.1.2 W
    (∀ y, y ∈ carrier ↔ y ∈ W ∧ (B.symm y.1,y.2) ∈
      round3PreparedParameterSecondaryCarrier Data r choice) ∧
    carrier ⊆ native.chart.source ∧ native.chart.source ⊆ W ∧
    IsClosed (Subtype.val ⁻¹' carrier : Set W) := by
  intro B W native carrier
  let q := round3ParameterProductChart (M := M) B
  have hOne (f : P × M → ℝ) (y : Ep × M) :
      y ∈ incrementsGlobalRelativeSupport W (fun z => f (B.symm z.1,z.2)) ↔
        y ∈ W ∧ (B.symm y.1,y.2) ∈ tsupport f := by
    rw [parameterRound2_global_relativeSupport_eq _ (B.open_target.prod isOpen_univ)]
    constructor
    · intro hy
      exact ⟨hy.1,(round3_prepared_native_tsupport_iff q f y hy.1).mp hy.2⟩
    · intro hy
      exact ⟨hy.1,(round3_prepared_native_tsupport_iff q f y hy.1).mpr hy.2⟩
  have hCarrier (y : Ep × M) : y ∈ carrier ↔ y ∈ W ∧
      (B.symm y.1,y.2) ∈ round3PreparedParameterSecondaryCarrier Data r choice := by
    constructor
    · rintro ⟨hy,hnu,hmu⟩
      have hn := (hOne (Data.cutoff r.val.1.1) y).mp hnu
      have hm := (hOne (Data.cutoff r.val.1.2) y).mp hmu
      exact ⟨hn.1,(round3_prepared_native_tsupport_iff q choice.cutoff y hn.1).mp hy,hn.2,hm.2⟩
    · rintro ⟨hy,hcut,hnu,hmu⟩
      exact ⟨(round3_prepared_native_tsupport_iff q choice.cutoff y hy).mpr hcut,
        (hOne (Data.cutoff r.val.1.1) y).mpr ⟨hy,hnu⟩,
        (hOne (Data.cutoff r.val.1.2) y).mpr ⟨hy,hmu⟩⟩
  refine ⟨hCarrier,?_,?_,?_⟩
  · intro y hy
    have hh := (hCarrier y).mp hy
    exact (round3ParameterChartPullback_source_iff B choice.chart hPreserves y hh.1.1).mpr
      (hSource hh.2)
  · intro y hy
    exact ⟨((round3ParameterChartPullback_source B choice.chart y).mp hy).1,mem_univ _⟩
  · exact ((isClosed_tsupport native.cutoff).preimage continuous_subtype_val).inter
      ((actual_relative_support_preimage_closed W (fun z => Data.cutoff r.val.1.1 (B.symm z.1,z.2))).inter
        (actual_relative_support_preimage_closed W (fun z => Data.cutoff r.val.1.2 (B.symm z.1,z.2))))

 theorem round3_prepared_parameter_native_cutoff_smooth
    (B : OpenPartialHomeomorph P Ep) (hB : B ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (rho : P × M → ℝ) (hRho : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ rho) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
      (fun y : Ep × M => rho (B.symm y.1,y.2)) (B.target ×ˢ (univ : Set M)) :=
  hRho.comp_contMDiffOn (round3ParameterProductChart_symm_smooth B hB)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_secondary_native_carrier
