import Probes.Round3ParameterNativeRefinementSamples

/-! Local-domain form of the existing exact refinement-sample construction.
Only the partition/support geometry is localized to W; every actual sample,
host transition, inverse, eta and numerical bound is the original one. This
is used below with geometry produced from the genuine open-parameter packet,
not as a replacement for producing that packet. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
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
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem fullIncrementNov_native_refinement_samples_from_local_geometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    {Sub : Type*} [Fintype Sub]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (R : ℕ)
    (ip : Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Sub → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Sub → OpenPartialHomeomorph X X)
    (hChart : ∀ nu a, actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a) =
      (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart ip)).chart nu a)
    (hSource : ∀ nu a, (b nu a).source ⊆ (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart (host nu a))).target)
    (hInner : ∀ nu a y, y ∈ ((round3ParameterNativePrimary (fun p x => Data.F (p,x)) g
      (Data.parameterChart ip)).chart nu a).source → y.2 ∈ Data.atlas.inner (host nu a))
    (Forward Inverse Meta : ℕ → ℝ)
    (hProfiles : Round3ParameterOriginalChartProfiles Data g Forward Inverse Meta)
    (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (W : Set (Ep × M)) (hW : IsOpen W) (hWB : W ⊆ (Data.parameterChart ip).target ×ˢ (univ : Set M))
    (hGeo :
      let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart ip)
      (∀ nu a, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (gN.eta nu a) W) ∧
      (∀ nu a, incrementsGlobalRelativeSupport W (gN.eta nu a) ⊆ (gN.chart nu a).source) ∧
      (∀ nu z, z ∈ incrementsGlobalRelativeSupport W (gN.cutoff nu) →
        ∀ᶠ w in 𝓝 z, ∑ a, gN.eta nu a w = 1) ∧
      (∀ nu z, z ∈ W → (Finset.univ.filter
        (fun a => z ∈ incrementsGlobalRelativeSupport W (gN.eta nu a))).card ≤ R) ∧
      ∀ z, z ∈ W → (Finset.univ.filter
        (fun nu => z ∈ incrementsGlobalRelativeSupport W (gN.cutoff nu))).card ≤ Data.primaryCount) :
    let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart ip)
    Round3ParameterRefinementSamples Data ip (fun p x => Data.F ((Data.parameterChart ip).symm p,x))
      gN host b W ell Inverse
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) R Data.primaryCount := by
  intro gN
  let Active := round3ParameterRefinementActive Data ip _ gN W
  have hEta (observer nu a) (z : X) (hz : z ∈ Active observer nu a) :
      (z.1,(Data.atlas.chart observer).symm z.2) ∈ incrementsGlobalRelativeSupport W (gN.eta nu a) := by
    obtain ⟨w,hw,heq⟩ := hz.2
    exact ⟨w,tsupport_mul_subset_left hw,heq⟩
  have hPhysicalEta (observer nu a) (z : X) (hz : z ∈ Active observer nu a) :
      ((Data.parameterChart ip).symm z.1,(Data.atlas.chart observer).symm z.2) ∈ tsupport (g.eta nu a) := by
    have he := hEta observer nu a z hz
    rw [parameterRound2_global_relativeSupport_eq W hW] at he
    exact round3Parameter_plain_pullback_tsupport (round3ParameterProductChart (M := M) (Data.parameterChart ip))
      (g.eta nu a) _ (hWB he.1) he.2
  have hHostSample (observer nu a) (z : X) (hz : z ∈ Active observer nu a) :
      parameterTensorModelEquiv (m+1) d
        (z.1,Data.atlas.chart (host nu a) ((Data.atlas.chart observer).symm z.2)) ∈
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain
        Data.parameterSet (host nu a,ip) := by
    have hsrc := hGeo.2.1 nu a (hEta observer nu a z hz)
    have hobs := (actual_original_native_evaluation_iff Data hd (observer,ip) z).mp hz.1.1
    exact (actual_original_native_evaluation_iff Data hd (host nu a,ip) _).mpr
      ⟨hd.source_inner_norm (host nu a) _ (hInner nu a _ hsrc),hobs.2⟩
  have hJets (observer nu a) (k : ℕ) (z : X) (hz : z ∈ Active observer nu a) :
      let y := (z.1,(Data.atlas.chart observer).symm z.2)
      let w := (z.1,Data.atlas.chart (host nu a) y.2)
      ell^(k-1)*‖iteratedFDeriv ℝ k (b nu a).symm (gN.chart nu a y)‖ ≤ Inverse k ∧
      ell^(k-1)*‖iteratedFDeriv ℝ k (b nu a) w‖ ≤ Forward k ∧
      ell^k*‖iteratedFDeriv ℝ k (gN.eta nu a ∘ (gN.chart nu a).symm) (gN.chart nu a y)‖ ≤ Meta k := by
    intro y w
    let c := Data.atlas.chart (host nu a)
    let q := actualOriginalHostJointChart («Ep» := Ep) c
    let t := q.symm.trans (gN.chart nu a)
    have hsrc := hGeo.2.1 nu a (hEta observer nu a z hz)
    have hInnerY := hInner nu a y hsrc
    have hyc : y.2 ∈ c.source := Data.atlas.inner_subset (host nu a) hInnerY
    have hw : q.symm w = y := by
      change (z.1,c.symm (c y.2)) = y
      rw [c.left_inv hyc]
    have hpoint : t w = gN.chart nu a y := congrArg (gN.chart nu a) hw
    have hPhys : ((Data.parameterChart ip).symm w.1,c.symm w.2) ∈ tsupport (g.eta nu a) := by
      change ((Data.parameterChart ip).symm z.1,c.symm (c y.2)) ∈ _
      rw [c.left_inv hyc]
      exact hPhysicalEta observer nu a z hz
    have hh := hProfiles ell hell hell1 nu a (host nu a,ip) k w (hHostSample observer nu a z hz) hPhys
    have hNative : w ∈ (b nu a).source := by
      rw [← hChart nu a] at hsrc
      exact hsrc.2
    have hbt : gN.chart nu a y ∈ (b nu a).target := by
      rw [← hChart nu a]
      exact (b nu a).map_source hNative
    have hj := round3_prepared_host_transition_jets c (b nu a) (hSource nu a)
    have hChartLocal : actualHostAdaptedChart c (b nu a) = gN.chart nu a := hChart nu a
    have hForw : iteratedFDeriv ℝ k t w = iteratedFDeriv ℝ k (b nu a) w := by
      simpa only [hChartLocal] using hj.1 k w hNative
    have hInv : iteratedFDeriv ℝ k t.symm (gN.chart nu a y) =
        iteratedFDeriv ℝ k (b nu a).symm (gN.chart nu a y) := by
      simpa only [hChartLocal] using hj.2 k _ hbt
    change w ∈ t.source ∧ t w ∈ t.target ∧
      ell^(k-1)*‖iteratedFDeriv ℝ k t w‖ ≤ Forward k ∧
      ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t w)‖ ≤ Inverse k ∧
      ell^k*‖iteratedFDeriv ℝ k (gN.eta nu a ∘ (gN.chart nu a).symm) (t w)‖ ≤ Meta k at hh
    rw [hpoint,hForw,hInv] at hh
    exact ⟨hh.2.2.2.1,hh.2.2.1,hh.2.2.2.2⟩
  refine {
    eta_smooth := hGeo.1
    eta_support := hGeo.2.1
    partition := hGeo.2.2.1
    sample_inverse := ?_
    inverse_jets := ?_
    forward_jets := ?_
    eta_jets := ?_
    eta_count := hGeo.2.2.2.1
    primary_count := hGeo.2.2.2.2 }
  · intro observer nu a y hy
    obtain ⟨z,hz,rfl⟩ := hy
    have hsrc := hGeo.2.1 nu a (hEta observer nu a z hz)
    rw [← hChart nu a] at hsrc ⊢
    change (b nu a).symm ((b nu a) (z.1,Data.atlas.chart (host nu a) ((Data.atlas.chart observer).symm z.2))) ∈ _
    have hb : (z.1,Data.atlas.chart (host nu a) ((Data.atlas.chart observer).symm z.2)) ∈ (b nu a).source := hsrc.2
    rw [(b nu a).left_inv hb]
    exact hHostSample observer nu a z hz
  · intro observer nu a k hk y hy
    obtain ⟨z,hz,rfl⟩ := hy
    exact (hJets observer nu a k z hz).1
  · intro r observer nu a k hk hkr z hz
    exact ((hJets observer nu a k z hz).2.1).trans
      (round3PreparedFiniteMaximum_bound (fun l : Fin (r+2) => Forward l) ⟨k,by omega⟩)
  · intro r observer nu a k hkr y hy
    obtain ⟨z,hz,rfl⟩ := hy
    exact ((hJets observer nu a k z hz).2.2).trans
      (round3PreparedFiniteMaximum_bound (fun l : Fin (r+1) => Meta l) ⟨k,by omega⟩)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_native_refinement_samples_from_local_geometry
