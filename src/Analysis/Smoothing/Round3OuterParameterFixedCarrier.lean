import Smoothing.Round3OuterFixedCarrier

/-! Actual original primary geometry with a fixed effective carrier.
The same physical charts are restricted, keeping their forward/inverse
functions. The new eta is the explicitly constructed common scalar plateau
times the original eta. Its entire topological support lies in the genuine
open normal domain, which is covered by ORIGINAL nonzero eta regions.
No current smoothed-map norm or quantitative reserve is assumed here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
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
local notation "𝓙" => 𝓘(ℝ,D)

def round3ParameterFixedCarrierFamily
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := A) (fun p x => Data.F (p,x)))
    (hOpen : ∀ nu, IsOpen (round3FixedCarrierDomain (g.eta nu))) :
    Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := A) (fun p x => Data.F (p,x)) where
  phase := g.phase
  cutoff := g.cutoff
  normal := g.normal
  linearArgument := g.linearArgument
  eta := fun nu => round3FixedCarrierCutoff (g.eta nu)
  chart := fun nu a => (g.chart nu a).restrOpen (round3FixedCarrierDomain (g.eta nu)) (hOpen nu)
  inverse := g.inverse
  normal_mem := fun nu a z hz => g.normal_mem nu a z hz.1

theorem round3_parameter_original_fixed_carrier
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := A) (fun p x => Data.F (p,x)))
    (R : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry Data g R) :
    let domain := fun nu => round3FixedCarrierDomain (g.eta nu)
    ∃ hOpen : ∀ nu, IsOpen (domain nu),
      (∀ nu, tsupport (Data.cutoff nu) ⊆ domain nu) ∧
      (∀ nu, domain nu ⊆ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) ∧
      (∀ nu z, z ∈ domain nu → ∃ a, g.eta nu a z ≠ 0) ∧
      let E := {Data with primaryDomain := domain}
      let out := round3ParameterFixedCarrierFamily Data g hOpen
      Round3ParameterOriginalPrimaryGeometry E out R ∧
      (∀ nu a, ((out.chart nu a) : P × M → P × D) = g.chart nu a) ∧
      (∀ nu a, (((out.chart nu a).symm) : P × D → P × M) = (g.chart nu a).symm) ∧
      out.inverse = g.inverse ∧
      (∀ nu a, tsupport (out.eta nu a) ⊆ tsupport (g.eta nu a) ∩ domain nu) := by
  intro domain
  have hCar (nu : Fin Data.primaryCount) := round3_fixed_cutoff_carrier
    (I := (𝓘(ℝ,Ep)).prod 𝓙) (g.eta nu) (tsupport (Data.cutoff nu)) R
    (geom.smooth nu) (geom.compact nu) (geom.partition nu) (geom.count nu)
  let hOpen := fun nu => (hCar nu).open_domain
  have hSubset : ∀ nu, domain nu ⊆ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data := by
    intro nu z hz
    obtain ⟨a,ha⟩ := (hCar nu).active z hz
    have hSource := geom.support nu a (subset_tsupport (g.eta nu a) ha)
    have hTarget := (g.chart nu a).map_source hSource
    have hActive := geom.inverse_active nu a _ hTarget
    have hPoint : ((g.chart nu a z).1,g.inverse nu a (g.chart nu a z).1 (g.chart nu a z).2) = z := by
      rw [← geom.inverse nu a _ hTarget,(g.chart nu a).left_inv hSource]
    rwa [hPoint] at hActive
  refine ⟨hOpen,fun nu => (hCar nu).covers,hSubset,fun nu z hz => (hCar nu).active z hz,?_⟩
  let E := {Data with primaryDomain := domain}
  let out := round3ParameterFixedCarrierFamily Data g hOpen
  change Round3ParameterOriginalPrimaryGeometry E out R ∧ _
  refine ⟨?_,fun _ _ => rfl,fun _ _ => rfl,rfl,fun nu a => (hCar nu).support a⟩
  exact {
    phase := geom.phase
    cutoff := geom.cutoff
    normal := geom.normal
    linear := geom.linear
    preserves := fun nu a z hz => geom.preserves nu a z hz.1
    inverse := fun nu a z hz => geom.inverse nu a z hz.1
    phase_coordinate := fun nu a z hz => geom.phase_coordinate nu a z hz.1
    inverse_active := by
      intro nu a z hz
      change (z.1,g.inverse nu a z.1 z.2) ∈ domain nu ∩ incrementsOriginalParameterRegion Data
      exact ⟨by rw [← geom.inverse nu a z hz.1]; exact hz.2,
        (geom.inverse_active nu a z hz.1).2⟩
    smooth := fun nu => (hCar nu).smooth
    compact := fun nu => (hCar nu).compact
    support := by
      intro nu a z hz
      have hh := (hCar nu).support a hz
      exact ⟨geom.support nu a hh.1,hh.2⟩
    partition := fun nu => (hCar nu).partition
    count := fun nu => (hCar nu).count }

#print axioms round3_parameter_original_fixed_carrier
end GlobalEmbedding.Continuation
