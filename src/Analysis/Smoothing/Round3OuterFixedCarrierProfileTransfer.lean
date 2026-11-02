import Smoothing.Round3OuterParameterFixedReferenceProfiles
import Probes.Round3ParameterFixedProfileRebase

/-! Fixed reference profiles of the one explicit plateau are transported
to every later actual stable family by literal function identities.
There is no compact maximization or new cutoff choice after SF. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
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

theorem round3_fixed_carrier_profiles_same_functions
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref)
    (g0 g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Ref.primaryCount) (Β := A) (fun p x => Ref.F (p,x)))
    (R : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry Ref g R)
    (hEta : g.eta = g0.eta)
    (hForward : ∀ nu a, ((g.chart nu a) : P × M → P × D) = g0.chart nu a)
    (hInverse : ∀ nu a, ((g.chart nu a).symm : P × D → P × M) = (g0.chart nu a).symm)
    (hOpen0 : ∀ nu, IsOpen (round3FixedCarrierDomain (g0.eta nu)))
    (hOpen : ∀ nu, IsOpen (round3FixedCarrierDomain (g.eta nu)))
    (Forward Inverse Meta : ℕ → ℝ)
    (hProfile : Round3ParameterOriginalChartProfiles Ref
      (round3ParameterFixedCarrierFamily Ref g0 hOpen0) Forward Inverse Meta) :
    let out := round3ParameterFixedCarrierFamily Ref g hOpen
    Round3ParameterOriginalPrimaryGeometry Ref out R ∧
      Round3ParameterOriginalChartProfiles Ref out Forward Inverse Meta ∧
      out.eta = (round3ParameterFixedCarrierFamily Ref g0 hOpen0).eta := by
  intro out
  obtain ⟨hO,hCover,hSub,hActive,hGeom,rest⟩ := round3_parameter_original_fixed_carrier Ref g R geom
  have hg : Round3ParameterOriginalPrimaryGeometry Ref out R := {
    hGeom with
    inverse_active := fun nu a z hz =>
      ⟨(hSub nu (hGeom.inverse_active nu a z hz).1).1,(hGeom.inverse_active nu a z hz).2⟩ }
  let old := round3ParameterFixedCarrierFamily Ref g0 hOpen0
  have hNewEta : out.eta = old.eta := by
    change (fun nu => round3FixedCarrierCutoff (g.eta nu)) =
      (fun nu => round3FixedCarrierCutoff (g0.eta nu))
    rw [hEta]
  have hNewForward (nu) (a) : ((out.chart nu a) : P × M → P × D) = old.chart nu a := hForward nu a
  have hNewInverse (nu) (a) : ((out.chart nu a).symm : P × D → P × M) = (old.chart nu a).symm := hInverse nu a
  refine ⟨hg,?_,hNewEta⟩
  exact round3Parameter_original_profiles_stage_rebase Ref hd old Forward Inverse Meta hProfile
    Ref.F Ref.H Ref.parameterOpen Ref.freeNormal Ref.primaryDomain Ref.tensorNeighborhood
    out R hg hNewEta hNewForward hNewInverse

#print axioms round3_fixed_carrier_profiles_same_functions
end GlobalEmbedding.Continuation
