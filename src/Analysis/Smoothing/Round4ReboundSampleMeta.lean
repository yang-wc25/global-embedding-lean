import Smoothing.Round4FixedCarrierEtaGerm
import Smoothing.Round3OuterParameterFixedCarrier
import Probes.Round3ParameterNativeRefinementSamples
import Probes.Round3ParameterFixedProfileRebase

/-! On the actual original repair samples the fixed-carrier plateau is one
as a germ. The exact native refinement-sample structure therefore consumes
the original family's Meta profile, without any high-order compact maximum
for the auxiliary fixed-carrier plateau. No global equality of eta is claimed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P A : Type*} [TopologicalSpace M] [TopologicalSpace P] [Fintype A]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × Es
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,Es)

theorem round4_actual_rebound_refinement_sample_meta
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (g0 : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Ref.primaryCount) (Β := A) (fun p x => Ref.F (p,x)))
    (R : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry Ref g0 R)
    (Forward Inverse Meta : ℕ → ℝ)
    (hProfiles : Round3ParameterOriginalChartProfiles Ref g0 Forward Inverse Meta)
    (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (V : Set P) (normal : Fin Ref.primaryCount → P × M → Ey)
    (domain : Fin Ref.primaryCount → Set (P × M))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm})
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Ref.primaryCount) (Β := A) (fun p x => F (p,x)))
    (hCutoff : g.cutoff = Ref.cutoff)
    (hEta : g.eta = fun nu => round3FixedCarrierCutoff (g0.eta nu))
    (hForward : ∀ nu a, ((g.chart nu a) : P × M → P × Es) = g0.chart nu a)
    (hInverse : ∀ nu a, ((g.chart nu a).symm : P × Es → P × M) = (g0.chart nu a).symm)
    (ip : Fin Ref.parameterCount)
    (host : Fin Ref.primaryCount → A → Fin Ref.atlas.count)
    (b : Fin Ref.primaryCount → A → OpenPartialHomeomorph X X)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hWB : W ⊆ (Ref.parameterChart ip).target ×ˢ (univ : Set M))
    (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (SampleInverse SampleForward OldMeta : ℕ → ℝ) (Rsub Lprimary : ℕ) :
    let E := round3ParameterStageData Ref F H V normal domain neighborhood
    let gN := round3ParameterNativePrimary (fun p x => F (p,x)) g (Ref.parameterChart ip)
    Round3ParameterRefinementSamples E ip (fun p x => F ((Ref.parameterChart ip).symm p,x))
      gN host b W ell SampleInverse SampleForward OldMeta Rsub Lprimary →
    Round3ParameterRefinementSamples E ip (fun p x => F ((Ref.parameterChart ip).symm p,x))
      gN host b W ell SampleInverse SampleForward
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) Rsub Lprimary := by
  intro E gN hSamples
  refine { hSamples with eta_jets := ?_ }
  intro r observer nu a k hkr z hz
  change Fin Ref.atlas.count at observer
  change Fin Ref.primaryCount at nu
  obtain ⟨w,hw,rfl⟩ := hz
  let y : Ep × M := (w.1,(Ref.atlas.chart observer).symm w.2)
  let physical : P × M := ((Ref.parameterChart ip).symm w.1,(Ref.atlas.chart observer).symm w.2)
  let originalN := round3ParameterNativePrimary (fun p x => Ref.F (p,x)) g0 (Ref.parameterChart ip)
  have hCutNative : y ∈ incrementsGlobalRelativeSupport W (gN.cutoff nu) := hw.1.2
  rw [parameterRound2_global_relativeSupport_eq W hW] at hCutNative
  have hEtaNative : y ∈ incrementsGlobalRelativeSupport W (gN.eta nu a) := by
    obtain ⟨v,hv,heq⟩ := hw.2
    exact ⟨v,tsupport_mul_subset_left hv,heq⟩
  rw [parameterRound2_global_relativeSupport_eq W hW] at hEtaNative
  have hCutPhysical : physical ∈ tsupport (Ref.cutoff nu) := by
    have hh := round3Parameter_plain_pullback_tsupport
      (round3ParameterProductChart (M := M) (Ref.parameterChart ip)) (g.cutoff nu)
      y (hWB hCutNative.1) hCutNative.2
    rwa [hCutoff] at hh
  have hEtaPhysical : physical ∈ tsupport (g0.eta nu a) := by
    have hh := round3Parameter_plain_pullback_tsupport
      (round3ParameterProductChart (M := M) (Ref.parameterChart ip)) (g.eta nu a)
      y (hWB hEtaNative.1) hEtaNative.2
    rw [hEta] at hh
    exact tsupport_mul_subset_right hh
  have hProfile := hProfiles ell hell hell1 nu a (observer,ip) k w hw.1.1 hEtaPhysical
  have hSource : y ∈ (originalN.chart nu a).source := hProfile.1.2
  have hTarget : originalN.chart nu a y ∈ (originalN.chart nu a).target :=
    (originalN.chart nu a).map_source hSource
  have hLeft := (originalN.chart nu a).left_inv hSource
  have hSum : ∀ᶠ v in 𝓝
      ((Ref.parameterChart ip).symm ((originalN.chart nu a).symm (originalN.chart nu a y)).1,
        ((originalN.chart nu a).symm (originalN.chart nu a y)).2), ∑ c, g0.eta nu c v = 1 := by
    rw [hLeft]
    exact geom.partition nu physical hCutPhysical
  have hJet := round4_fixed_carrier_native_eta_jet (Ref.parameterChart ip) (g0.chart nu a)
    (geom.preserves nu a) (g0.eta nu) a (originalN.chart nu a y) hTarget hSum k
  have hNativeForward : ((gN.chart nu a) : Ep × M → X) = originalN.chart nu a := by
    funext v
    change ((Ref.parameterChart ip) ((g.chart nu a) ((Ref.parameterChart ip).symm v.1,v.2)).1,
      ((g.chart nu a) ((Ref.parameterChart ip).symm v.1,v.2)).2) = _
    rw [hForward]
    rfl
  have hNativeInverse : ((gN.chart nu a).symm : X → Ep × M) = (originalN.chart nu a).symm := by
    funext v
    change ((Ref.parameterChart ip) ((g.chart nu a).symm ((Ref.parameterChart ip).symm v.1,v.2)).1,
      ((g.chart nu a).symm ((Ref.parameterChart ip).symm v.1,v.2)).2) = _
    rw [hInverse]
    rfl
  have hEtaFun : (gN.eta nu a ∘ (gN.chart nu a).symm) =
      (fun v : X => round3FixedCarrierCutoff (g0.eta nu) a
        ((Ref.parameterChart ip).symm ((originalN.chart nu a).symm v).1,
          ((originalN.chart nu a).symm v).2)) := by
    funext v
    change g.eta nu a ((Ref.parameterChart ip).symm ((gN.chart nu a).symm v).1,
      ((gN.chart nu a).symm v).2) = _
    rw [hEta,hNativeInverse]
  change ell^k*‖iteratedFDeriv ℝ k (gN.eta nu a ∘ (gN.chart nu a).symm)
    (gN.chart nu a y)‖ ≤ _
  change iteratedFDeriv ℝ k (fun v : X => round3FixedCarrierCutoff (g0.eta nu) a
      ((Ref.parameterChart ip).symm ((originalN.chart nu a).symm v).1,
        ((originalN.chart nu a).symm v).2)) (originalN.chart nu a y) =
    iteratedFDeriv ℝ k (originalN.eta nu a ∘ (originalN.chart nu a).symm)
      (originalN.chart nu a y) at hJet
  rw [hEtaFun,hNativeForward,hJet]
  exact hProfile.2.2.2.2.trans
    (round3PreparedFiniteMaximum_bound (fun l : Fin (r+1) => Meta l) ⟨k,by omega⟩)

#print axioms round4_actual_rebound_refinement_sample_meta
end GlobalEmbedding.Continuation
