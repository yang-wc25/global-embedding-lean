import Probes.Round3ParameterObserverChartProfiles
import Probes.Round3ParameterWholePrimaryFactory

/-! The genuine all-chart family has one simultaneous forward/inverse/eta
profile on EVERY original evaluation domain. Profiles are selected once,
before the derivative order and the later scale; all native derivatives are
total Ep×D derivatives, and samples are the literal original source-first
coordinate sets. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
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
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_actual_whole_primary_chart_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (S : (Fin Data.atlas.count × Fin Data.parameterCount) → Set (Fin (m+1+d) → ℝ))
    (hS : ∀ i, IsCompact (S i))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation Data.atlas Data.parameterChart i) :
    let g := round3ParameterWholePrimaryFamily Data hd hs hn theta packet
    ∃ Forward Inverse Meta : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Meta k) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ nu beta i,
      let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)
      let t := ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart i.1)).symm.trans (gN.chart nu beta)
      let etaN := fun z : X => gN.eta nu beta ((gN.chart nu beta).symm z)
      ∀ k z, parameterTensorModelEquiv (m+1) d z ∈ S i →
        ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈ tsupport (g.eta nu beta) →
        z ∈ t.source ∧ t z ∈ t.target ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ Forward k ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ Inverse k ∧
        ell^k*‖iteratedFDeriv ℝ k etaN (t z)‖ ≤ Meta k := by
  intro g
  let J := Fin Data.primaryCount × Round3ParameterWholePrimaryIndex Data theta packet ×
    (Fin Data.atlas.count × Fin Data.parameterCount)
  let Sn := fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' S i
  have hSn (i) : IsCompact (Sn i) :=
    (parameterTensorModelEquiv (m+1) d).toHomeomorph.isCompact_preimage.mpr (hS i)
  have hSnTarget (i) : Sn i ⊆ (Data.parameterChart i.2).target ×ˢ (Data.atlas.chart i.1).target := by
    intro z hz
    have hh := hSO i hz
    change ((parameterTensorModelEquiv (m+1) d).symm (parameterTensorModelEquiv (m+1) d z)).2 ∈
        (Data.atlas.chart i.1).target ∧
      ((parameterTensorModelEquiv (m+1) d).symm (parameterTensorModelEquiv (m+1) d z)).1 ∈
        (Data.parameterChart i.2).target at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply,mem_prod] using hh.symm
  have hChart (nu) (beta) := round3ParameterLiftedPrimaryChart_smooth Data hd beta.1.2 nu _
    (round3ParameterWholePrimaryPiece Data hd theta packet nu beta)
  have hEta (nu) (beta) := round3ParameterWholePrimaryFamily_cutoff_geometry Data hd hs hn theta packet nu beta
  have hPreserves := round3ParameterOriginalPrimaryFamily_preserves Data hd hs hn
    (fun (_ : Fin Data.primaryCount) (a : Round3ParameterWholePrimaryIndex Data theta packet) => a.1.2)
    (fun _ a => (Data.parameterChart a.1.2).target ×ˢ (univ : Set M))
    (round3ParameterWholePrimaryPiece Data hd theta packet)
  have hOne (j : J) := round3Parameter_actual_observer_chart_profiles
    (Data.parameterChart j.2.2.2) (hd.parameter_charts_smooth j.2.2.2)
    (g.chart j.1 j.2.1) (hPreserves j.1 j.2.1) (hChart j.1 j.2.1).1 (hChart j.1 j.2.1).2
    (g.eta j.1 j.2.1) (hEta j.1 j.2.1).1 (hEta j.1 j.2.1).2.2.2
    (Data.atlas.chart j.2.2.1) (hd.atlas_smooth.chart_mem j.2.2.1)
    (Sn j.2.2) (hSn j.2.2) (hSnTarget j.2.2)
  choose Tf Ti Te hTf hTi hTe hb using hOne
  refine ⟨fun k => round3PreparedFiniteMaximum (fun j : J => Tf j k),
    fun k => round3PreparedFiniteMaximum (fun j : J => Ti j k),
    fun k => round3PreparedFiniteMaximum (fun j : J => Te j k),
    fun k => round3PreparedFiniteMaximum_nonneg _,
    fun k => round3PreparedFiniteMaximum_nonneg _,
    fun k => round3PreparedFiniteMaximum_nonneg _,?_⟩
  intro ell hell hell1 nu beta i gN t etaN k z hz hEtaZ
  have hh := hb (nu,beta,i) ell hell hell1 k z ⟨hz,hEtaZ⟩
  exact ⟨hh.1,hh.2.1,
    hh.2.2.1.trans (round3PreparedFiniteMaximum_bound (fun j : J => Tf j k) (nu,beta,i)),
    hh.2.2.2.1.trans (round3PreparedFiniteMaximum_bound (fun j : J => Ti j k) (nu,beta,i)),
    hh.2.2.2.2.trans (round3PreparedFiniteMaximum_bound (fun j : J => Te j k) (nu,beta,i))⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_whole_primary_chart_profiles
