import Smoothing.Round3OuterParameterFixedCarrier
import Probes.Round3ParameterWholePrimaryChartProfiles
import Probes.Round3ParameterNativeRefinementSamples

/-! The explicit fixed-carrier primary family has actual all-observer
profiles selected from the reference geometry. Forward/inverse functions
are unchanged, eta is the one fixed plateau construction, and the finite
maximum is taken BEFORE every current SF and every later scale. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P A : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] [Fintype A]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_parameter_original_fixed_reference_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := A) (fun p x => Data.F (p,x)))
    (R : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry Data g R)
    (hChart : ∀ nu a, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (g.chart nu a) (g.chart nu a).source)
    (hInverse : ∀ nu a, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (g.chart nu a).symm (g.chart nu a).target)
    (hCompact : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i)) :
    ∃ Forward Inverse Meta : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Meta k) ∧
      Round3ParameterOriginalChartProfiles Data g Forward Inverse Meta := by
  let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
    Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
  let J := Fin Data.primaryCount × A × (Fin Data.atlas.count × Fin Data.parameterCount)
  let Sn := fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' S i
  have hSn (i) : IsCompact (Sn i) :=
    (parameterTensorModelEquiv (m+1) d).toHomeomorph.isCompact_preimage.mpr (hCompact i)
  have hTarget (i) : Sn i ⊆ (Data.parameterChart i.2).target ×ˢ (Data.atlas.chart i.1).target := by
    intro z hz
    have hh := (actual_original_native_evaluation_iff Data hd i z).mp hz
    exact ⟨hd.parameter_norm_subset i.2 hh.2.1,hd.source_norm_subset i.1 hh.1⟩
  have hOne (j : J) := round3Parameter_actual_observer_chart_profiles
    (Data.parameterChart j.2.2.2) (hd.parameter_charts_smooth j.2.2.2)
    (g.chart j.1 j.2.1) (geom.preserves j.1 j.2.1) (hChart j.1 j.2.1) (hInverse j.1 j.2.1)
    (g.eta j.1 j.2.1) (geom.smooth j.1 j.2.1) (geom.support j.1 j.2.1)
    (Data.atlas.chart j.2.2.1) (hd.atlas_smooth.chart_mem j.2.2.1)
    (Sn j.2.2) (hSn j.2.2) (hTarget j.2.2)
  choose Tf Ti Te hTf hTi hTe hb using hOne
  refine ⟨fun k => round3PreparedFiniteMaximum (fun j : J => Tf j k),
    fun k => round3PreparedFiniteMaximum (fun j : J => Ti j k),
    fun k => round3PreparedFiniteMaximum (fun j : J => Te j k),
    fun _ => round3PreparedFiniteMaximum_nonneg _,
    fun _ => round3PreparedFiniteMaximum_nonneg _,
    fun _ => round3PreparedFiniteMaximum_nonneg _,?_⟩
  intro ell hell hell1 nu a i gN t etaN k z hz hEta
  have hh := hb (nu,a,i) ell hell hell1 k z ⟨hz,hEta⟩
  exact ⟨hh.1,hh.2.1,
    hh.2.2.1.trans (round3PreparedFiniteMaximum_bound (fun j : J => Tf j k) (nu,a,i)),
    hh.2.2.2.1.trans (round3PreparedFiniteMaximum_bound (fun j : J => Ti j k) (nu,a,i)),
    hh.2.2.2.2.trans (round3PreparedFiniteMaximum_bound (fun j : J => Te j k) (nu,a,i))⟩

theorem round3_parameter_fixed_carrier_reference_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := A) (fun p x => Data.F (p,x)))
    (R : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry Data g R)
    (hChart : ∀ nu a, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (g.chart nu a) (g.chart nu a).source)
    (hInverse : ∀ nu a, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (g.chart nu a).symm (g.chart nu a).target)
    (hCompact : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i)) :
    ∃ hOpen : ∀ nu, IsOpen (round3FixedCarrierDomain (g.eta nu)),
    let out := round3ParameterFixedCarrierFamily Data g hOpen
    let E := {Data with primaryDomain := fun nu => round3FixedCarrierDomain (g.eta nu)}
    Round3ParameterOriginalPrimaryGeometry E out R ∧
    ∃ Forward Inverse Meta : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Meta k) ∧
      Round3ParameterOriginalChartProfiles E out Forward Inverse Meta := by
  obtain ⟨hOpen,hCover,hSub,hActive,hGeom,hForw,hInv,hInverseEq,hSupport⟩ :=
    round3_parameter_original_fixed_carrier Data g R geom
  let out := round3ParameterFixedCarrierFamily Data g hOpen
  have hGeomOld : Round3ParameterOriginalPrimaryGeometry Data out R := {
    hGeom with
    inverse_active := fun nu a z hz =>
      ⟨(hSub nu (hGeom.inverse_active nu a z hz).1).1,(hGeom.inverse_active nu a z hz).2⟩ }
  have hFwd : ∀ nu a, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (out.chart nu a) (out.chart nu a).source :=
    fun nu a => (hChart nu a).mono inter_subset_left
  have hBwd : ∀ nu a, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (out.chart nu a).symm (out.chart nu a).target :=
    fun nu a => (hInverse nu a).mono inter_subset_left
  exact ⟨hOpen,hGeom,round3_parameter_original_fixed_reference_profiles
    Data hd out R hGeomOld hFwd hBwd hCompact⟩

#print axioms round3_parameter_original_fixed_reference_profiles
#print axioms round3_parameter_fixed_carrier_reference_profiles
end GlobalEmbedding.Continuation
