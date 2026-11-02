import Smoothing.ParameterRound2MeanRawProfiles
import Probes.ActualIncrementPrimaryCoefficientBinding

/-! Original raw profiles produce the actual primary coefficient globally on
the observation domain. Active labels use their genuine positive open set;
inactive labels use the actual zero germ. No phase is differentiated outside
its original primary domain, and no coefficient/source/error output bound is
an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

 theorem actual_original_observed_coefficient_profiles_from_raw
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (c Bnd Mg : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    ∃ MD : ℝ, 0 ≤ MD ∧ ∀
      (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
      (e : OpenPartialHomeomorph M D)
      (he : ContMDiffOn I 𝓘(ℝ,D) ∞ e e.source)
      (heInv : ContMDiffOn 𝓘(ℝ,D) I ∞ e.symm e.target)
      (O S : Set X) (tau ell Delta : ℝ)
      (data : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n (q+2) j Rsub Lprimary c Bnd Mg T
        F hF g input inputbar W primary e O S tau ell Delta)
      (hTarget : ∀ z ∈ O, z.2 ∈ e.target) (nu : Λ),
    let coeff := fun z : X => incrementsGlobalObservedCoefficient F hF g input (q+2) tau e z.1 z.2 nu
    ContDiffOn ℝ ∞ coeff O ∧
      (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k coeff z‖ ≤ MD) ∧
      (∀ z ∈ O, (z.1,e.symm z.2) ∉ incrementsGlobalRelativeSupport W (g.cutoff nu) →
        coeff =ᶠ[𝓝 z] 0) := by
  obtain ⟨MC,hMC,hraw⟩ := parameterRound2_actual_primitive_globalCoefficient_profiles_uniform_split_scale
    (I := I) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N) (Λ := Λ) (Β := Β)
    n (q+2) j Rsub horder c Bnd Mg hc hBnd hMg T hT
  refine ⟨2*MC,by positivity,?_⟩
  intro F hF g input inputbar W primary e he heInv O S tau ell Delta data hTarget nu coeff
  let h := data.prim
  let Sample := S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff nu)
  let Pos := data.Omega nu ∩ {z | 0 < data.Lobs nu z (data.Aobs nu z)} ∩
    {z | 0 < data.Lobs nu z (data.Abarobs nu z)}
  let lead := fun z : X => incrementsGlobalObservedLeading F g input e z.1 z.2 nu
  let err := fun z : X => incrementsGlobalObservedError F hF g input (q+2) tau e z.1 z.2 nu
  have hp := hraw F hF g input inputbar nu W h.hW (h.hCombinedSupport nu) (h.hInverse nu) e
    (data.Omega nu) Sample (data.U nu) (data.Sloc nu) (data.hOmega nu) (data.hSOmega nu)
    (data.hkappa nu) (data.hmapW nu) (data.hU nu) (data.hOU nu) (data.hSloc nu) (data.hsource nu)
    (data.hphi nu) (data.hmap nu) (h.hA nu) (h.hB nu) (h.hG nu) (h.hJ nu) (h.hT0 nu)
    tau ell Delta data.htau data.htaul data.hell1 data.hDelta
    (parameterRound2_meanPrimitives_source F hF g input W primary h (q+2) tau nu)
    (parameterRound2_meanPrimitives_source F hF g inputbar W primary data.primbar (q+2) tau nu)
    (data.L nu) (data.A nu) (data.Abar nu) (data.hL nu) (data.hInput nu) (data.hInputbar nu)
    (data.hRep nu) (data.hRepbar nu) (data.hCut nu) (data.hEta nu) (data.hNormal nu) (data.hBR nu)
    (data.hReserve nu) (data.hBRb nu) (data.hLb nu) (data.hInputb nu) (data.hInputbarb nu)
    (data.hCutb nu) (data.hEtab nu) (data.hNormalb nu) (data.hDiff nu)
    (data.hAb nu) (data.hBb nu) (data.hGb nu) (data.hJb nu) (data.hTb nu)
    (data.hphib nu) (data.hRsub nu) (data.Lobs nu) (data.Aobs nu) (data.Abarobs nu)
    (data.hLobs nu) (data.hAobs nu) (data.hAbarobs nu) (data.hRepobs nu) (data.hRepbarobs nu)
    (data.hCutobs nu) (data.hNormalobs nu) (data.hPhaseobs nu) (data.hReserveobs nu)
    (data.hLobsb nu) (data.hAobsb nu) (data.hAbarobsb nu) (data.hCutobsb nu)
    (data.hNormalobsb nu) (data.hGradobsb nu) (data.hDiffobs nu)
  have hPos : IsOpen Pos := by
    have ha : IsOpen (data.Omega nu ∩ {z | 0 < data.Lobs nu z (data.Aobs nu z)}) :=
      ((data.hLobs nu).clm_apply (data.hAobs nu)).continuousOn.isOpen_inter_preimage (data.hOmega nu) isOpen_Ioi
    have hb : IsOpen (data.Omega nu ∩ {z | 0 < data.Lobs nu z (data.Abarobs nu z)}) :=
      ((data.hLobs nu).clm_apply (data.hAbarobs nu)).continuousOn.isOpen_inter_preimage (data.hOmega nu) isOpen_Ioi
    convert ha.inter hb using 1
    ext z
    simp only [Pos,Set.mem_inter_iff,Set.mem_ofPred_eq]
    tauto
  have hPosCover : O ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (g.cutoff nu) ⊆ Pos := by
    intro z hz
    exact ⟨⟨data.hCover nu hz,(data.hPositiveCover nu z hz).1⟩,(data.hPositiveCover nu z hz).2⟩
  have hlead : ContDiffOn ℝ ∞ lead Pos := hp.1.1
  have herr : ContDiffOn ℝ ∞ err Pos := hp.2.1.1
  have hbind := increments_global_primary_mean_binding F hF g input q hq tau data.htau W h.hW primary
    h.hPrimary h.hPrimarySupport h.hSourceW h.hChart h.hChartInv h.hInverse h.hCombinedSupport
    h.hPhase h.hCut h.hNormal h.hArgument h.hEta h.hPositive h.hUnit h.hPartition h.hSymm h.hDecomp
    h.hDouble h.hInteraction h.hG h.hJ h.hT0 h.hA h.hB h.hSecond
  have heq : EqOn coeff (fun z => lead z+err z) O := by
    intro z hz
    exact congrFun (hbind.2.2 e he heInv z.1 z.2 (hTarget z hz) (data.hmapWO hz)).1 nu
  have hzero : ∀ z ∈ O, (z.1,e.symm z.2) ∉ incrementsGlobalRelativeSupport W (g.cutoff nu) →
      coeff =ᶠ[𝓝 z] 0 := by
    intro z hz hn
    have hh := parameterRound2_actual_globalObserved_inactive_germ F hF g input (q+2) tau
      W h.hW nu (h.hCombinedSupport nu) (h.hInverse nu) e O data.hO data.hkappaO data.hmapWO z hz hn
    filter_upwards [data.hO.mem_nhds hz,hh.1,hh.2] with w hw hwL hwE
    rw [heq hw]
    change incrementsGlobalObservedLeading F g input e w.1 w.2 nu +
      incrementsGlobalObservedError F hF g input (q+2) tau e w.1 w.2 nu = 0
    simp only [hwL,hwE,Pi.zero_apply,add_zero]
  have hsmooth : ContDiffOn ℝ ∞ coeff O := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    by_cases ha : (z.1,e.symm z.2) ∈ incrementsGlobalRelativeSupport W (g.cutoff nu)
    · have heqg : coeff =ᶠ[𝓝 z] (fun w => lead w+err w) :=
        eventuallyEq_of_mem (data.hO.mem_nhds hz) (fun w hw => heq hw)
      exact ((hlead.add herr).contDiffAt (hPos.mem_nhds (hPosCover ⟨hz,ha⟩))).congr_of_eventuallyEq heqg
    · exact (contDiffAt_const (c := (0 : Fin (m+1) → Fin N → ℂ))).congr_of_eventuallyEq (hzero z hz ha)
  refine ⟨hsmooth,?_,hzero⟩
  intro k hk z hz
  by_cases ha : (z.1,e.symm z.2) ∈ incrementsGlobalRelativeSupport W (g.cutoff nu)
  · have hzPos := hPosCover ⟨data.hSO hz,ha⟩
    have heqg : coeff =ᶠ[𝓝 z] (fun w => lead w+err w) :=
      eventuallyEq_of_mem (data.hO.mem_nhds (data.hSO hz)) (fun w hw => heq hw)
    rw [(heqg.iteratedFDeriv ℝ k).eq_of_nhds]
    have hh := actual_joint_slow_add_jet_bound lead err k ell MC (MC*(tau/ell))
      (data.htau.trans_le data.htaul).le z
      ((hlead.contDiffAt (hPos.mem_nhds hzPos)).of_le (by simp))
      ((herr.contDiffAt (hPos.mem_nhds hzPos)).of_le (by simp))
      (hp.2.2.1 k hk z ⟨hz,ha⟩) (hp.2.2.2.2.1 k hk z ⟨hz,ha⟩)
    have hr : tau/ell ≤ 1 := (div_le_one (data.htau.trans_le data.htaul)).2 data.htaul
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hr hMC])
  · rw [((hzero z (data.hSO hz) ha).iteratedFDeriv ℝ k).eq_of_nhds]
    simpa using (mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hMC)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_observed_coefficient_profiles_from_raw
