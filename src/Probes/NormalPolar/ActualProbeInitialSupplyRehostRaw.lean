import NormalPolar.ActualProbeInitialSupplyRawScalarize
import NormalPolar.PassiveRawObserverPrimaryTransfer
import NormalPolar.PassiveRawObserverPhase
import Probes.ActualIncrementRawObserverDomains
import Probes.ActualRawProfileRestriction

/-! The same actual background in an additional observer.  Compact overlap
geometry chooses the transfer costs before the original raw record and all
scales.  Only the fixed primitive phase gradient is supplied separately;
`passiveOriginal_signed_observer_fields` produces that primitive profile on
the actual signed samples.  All tensor arguments, supports, subordinate
coordinate transitions and observer domains are produced here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M Λ Β : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

theorem actualProbeInitialSupply_raw_rehost_uniform
    (e host : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas IM ∞ M) (hh : host ∈ maximalAtlas IM ∞ M)
    (R : Set X) (hR : IsCompact R)
    (hRO : R ⊆ passiveOriginalObserverDomain (OpenPartialHomeomorph.refl Ep) e host) :
    ∃ C : ℕ → ℝ → ℝ → ℝ, ∃ Tgeo : ℕ → ℝ,
      (∀ k, 0 ≤ Tgeo k) ∧
      (∀ j B Ph, 0 ≤ B → 0 ≤ Ph → 0 ≤ C j B Ph) ∧
      ∀ (n length j Rsub Lprimary : ℕ) (reserve Bnd Mg : ℝ) (hBnd : 0 ≤ Bnd)
        (Tbackground : ℕ → ℝ) (hTbackground : ∀ k, 0 ≤ Tbackground k)
        (F : Ep → M → V) (hF : ∀ p, ContMDiff IM 𝓘(ℝ,V) ∞ (F p))
        (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
        (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
        (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
        (O S : Set X) (tau ell : ℝ)
        (data : ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n length j Rsub Lprimary
          reserve Bnd Mg Tbackground F hF g input input W primary e O S tau ell 0),
        MapsTo (passiveRawObserverTransition e host) R S →
        ∀ Ph : ℝ, 0 ≤ Ph →
        (∀ nu r k, k ≤ j → ∀ z ∈ R,
          (z.1,host.symm z.2) ∈ incrementsGlobalRelativeSupport W (g.cutoff nu) →
          ell^k*‖iteratedFDeriv ℝ k (fun w : X => fderiv ℝ
            (fun y => g.phase nu (w.1,host.symm y)) w.2 (EuclideanSpace.single r 1)) z‖ ≤ Ph) →
        Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n length j Rsub Lprimary
          reserve (C j Bnd Ph) Mg
          (fun k => actualFastChartTransferPrefix Tgeo k*bufferedTransitionPrefix Tbackground k)
          F hF g input input W primary host (actualRawObserverOpen host W) R tau ell 0) := by
  obtain ⟨Ta,hTa,hArg⟩ := passiveRaw_observer_argument_jets (Tr := ℝ)
    (N := N) (Λ := Λ) (Β := Β) e host he hh R hR hRO
  obtain ⟨Tc,hTc,hCut⟩ := passiveRaw_observer_field_transfer (Y := ℝ) e host he hh R hR hRO
  obtain ⟨Tn,hTn,hNormal⟩ := passiveRaw_observer_field_transfer (Y := V) e host he hh R hR hRO
  obtain ⟨Tg,hTg,hChart⟩ := passiveRaw_observer_primary_chart_jets (Tr := ℝ)
    (N := N) (Λ := Λ) (Β := Β) e host he hh R hR hRO
  let C : ℕ → ℝ → ℝ → ℝ := fun j B Ph => 1+B+
    actualFastChartTransferPrefix Ta (j+1)*(2^(j+1)*B^2)+
    actualFastChartTransferPrefix Tc (j+1)*B+
    actualFastChartTransferPrefix Tn (j+1)*B+Ph
  refine ⟨C,Tg,hTg,?_,?_⟩
  · intro j B Ph hB hPh
    have ha := actualFastChartTransferPrefix_nonneg Ta hTa (j+1)
    have hc := actualFastChartTransferPrefix_nonneg Tc hTc (j+1)
    have hn := actualFastChartTransferPrefix_nonneg Tn hTn (j+1)
    dsimp only [C]
    positivity
  intro n length j Rsub Lprimary reserve Bnd Mg hBnd Tbackground hTbackground
    F hF g input W primary O S tau ell data hSample Ph hPh hGrad
  let phi := passiveRawObserverTransition (d := d) e host
  let kappa := fun z : X => (z.1,host.symm z.2)
  let Onew := actualRawObserverOpen host W
  let Omega := fun nu => Onew ∩ kappa ⁻¹' primary nu
  let U := fun nu beta => Onew ∩ kappa ⁻¹' (g.chart nu beta).source
  let arg := fun nu (z : X) => g.linearArgument nu z.1 (host.symm z.2)
    (input z.1 (host.symm z.2))
  have hpoint (z : X) (hz : z ∈ R) : ((phi z).1,e.symm (phi z).2) = kappa z :=
    passiveRawObserverTransition_point e host z (hRO hz)
  have hRS : R ⊆ Onew := by
    intro z hz
    refine ⟨⟨mem_univ _,(hRO hz).2.1⟩,?_⟩
    change kappa z ∈ W
    rw [← hpoint z hz]
    exact data.hmapWO (data.hSO (hSample hz))
  have domains := actual_raw_observer_domains F hF g input W primary data.prim host
    (contMDiffOn_symm_of_mem_maximalAtlas hh) R hRS
  have hk : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod IM) ∞ kappa (univ ×ˢ host.target) :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      ((contMDiffOn_symm_of_mem_maximalAtlas hh).comp
        contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2))
  have hkOm nu : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod IM) ∞ kappa (Omega nu) :=
    hk.mono (fun _ hz => hz.1.1)
  have hMapOm nu : MapsTo kappa (Omega nu) (W ∩ primary nu) :=
    (domains.2.2.2.1 nu).2.2.2
  have hArgSmooth nu : ContDiffOn ℝ ∞ (arg nu) (Omega nu) :=
    ((data.prim.hArgument nu).comp (hkOm nu) (hMapOm nu)).contDiffOn
  have hCutSmooth nu : ContDiffOn ℝ ∞ (fun z : X => g.cutoff nu (kappa z)) (Omega nu) :=
    ((data.prim.hCut nu).comp (hkOm nu) (hMapOm nu)).contDiffOn
  have hNormalSmooth nu : ContDiffOn ℝ ∞ (fun z : X => g.normal nu (kappa z)) (Omega nu) :=
    ((data.prim.hNormal nu).comp (hkOm nu) (hMapOm nu)).contDiffOn
  have hPhaseSmooth nu : ContDiffOn ℝ ∞ (fun z : X => g.phase nu (kappa z)) (Omega nu) :=
    ((data.prim.hPhase nu).comp (hkOm nu) (hMapOm nu)).contDiffOn
  have hOld nu (z : X) (hz : z ∈ R)
      (ha : kappa z ∈ incrementsGlobalRelativeSupport W (g.cutoff nu)) :
      phi z ∈ S ∩ (fun w : X => (w.1,e.symm w.2)) ⁻¹'
        incrementsGlobalRelativeSupport W (g.cutoff nu) := by
    refine ⟨hSample hz,?_⟩
    change ((phi z).1,e.symm (phi z).2) ∈ incrementsGlobalRelativeSupport W (g.cutoff nu)
    rw [hpoint z hz]
    exact ha
  have hArgEq nu (z : X) (hz : z ∈ R)
      (ha : kappa z ∈ incrementsGlobalRelativeSupport W (g.cutoff nu)) :
      data.Lobs nu (phi z) (data.Aobs nu (phi z)) = arg nu z := by
    rw [data.hRepobs nu (phi z) (data.hSOmega nu (hOld nu z hz ha))]
    have hx := congrArg Prod.snd (hpoint z hz)
    change g.linearArgument nu z.1 (e.symm (e (host.symm z.2)))
      (input z.1 (e.symm (e (host.symm z.2)))) = _
    rw [show e.symm (e (host.symm z.2)) = host.symm z.2 from hx]
  have hpa := actualFastChartTransferPrefix_nonneg Ta hTa (j+1)
  have hpc := actualFastChartTransferPrefix_nonneg Tc hTc (j+1)
  have hpn := actualFastChartTransferPrefix_nonneg Tn hTn (j+1)
  have ha0 : 0 ≤ actualFastChartTransferPrefix Ta (j+1)*(2^(j+1)*Bnd^2) := by positivity
  have hc0 : 0 ≤ actualFastChartTransferPrefix Tc (j+1)*Bnd := mul_nonneg hpc hBnd
  have hn0 : 0 ≤ actualFastChartTransferPrefix Tn (j+1)*Bnd := mul_nonneg hpn hBnd
  have h1 : 1 ≤ C j Bnd Ph := by dsimp [C]; linarith
  have hB : Bnd ≤ C j Bnd Ph := by dsimp [C]; linarith
  have hA : actualFastChartTransferPrefix Ta (j+1)*(2^(j+1)*Bnd^2) ≤ C j Bnd Ph := by dsimp [C]; linarith
  have hC : actualFastChartTransferPrefix Tc (j+1)*Bnd ≤ C j Bnd Ph := by dsimp [C]; linarith
  have hN : actualFastChartTransferPrefix Tn (j+1)*Bnd ≤ C j Bnd Ph := by dsimp [C]; linarith
  have hP : Ph ≤ C j Bnd Ph := by dsimp [C]; linarith
  have hId (k : ℕ) (z : X) :
      ell^k*‖iteratedFDeriv ℝ k (fun _ : X => ContinuousLinearMap.id ℝ ℝ) z‖ ≤ C j Bnd Ph := by
    by_cases hk0 : k = 0
    · subst k
      simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using
        (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ)).trans h1
    · rw [iteratedFDeriv_const_of_ne hk0]
      simpa using zero_le_one.trans h1
  have hArgs nu k (hk : k ≤ j+1) z (hz : z ∈ R)
      (ha : kappa z ∈ incrementsGlobalRelativeSupport W (g.cutoff nu)) :
      ell^k*‖iteratedFDeriv ℝ k (arg nu) z‖ ≤ C j Bnd Ph :=
    (hArg n length j Rsub Lprimary reserve Bnd Mg Tbackground F hF g input input W primary
      O S tau ell 0 data hSample nu k hk z hz ha).trans hA
  have hCuts nu k (hk : k ≤ j+1) z (hz : z ∈ R)
      (ha : kappa z ∈ incrementsGlobalRelativeSupport W (g.cutoff nu)) :
      ell^k*‖iteratedFDeriv ℝ k (fun w : X => g.cutoff nu (kappa w)) z‖ ≤ C j Bnd Ph := by
    let Sold := S ∩ (fun w : X => (w.1,e.symm w.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (g.cutoff nu)
    exact (hCut (g.cutoff nu) (data.Omega nu) Sold (data.hOmega nu) (data.hSOmega nu)
      (data.hCutobs nu) (j+1) ell Bnd (data.htau.trans_le data.htaul) data.hell1 hBnd
      (data.hCutobsb nu) k hk z hz (hOld nu z hz ha)).trans hC
  have hNormals nu k (hk : k ≤ j+1) z (hz : z ∈ R)
      (ha : kappa z ∈ incrementsGlobalRelativeSupport W (g.cutoff nu)) :
      ell^k*‖iteratedFDeriv ℝ k (fun w : X => g.normal nu (kappa w)) z‖ ≤ C j Bnd Ph := by
    let Sold := S ∩ (fun w : X => (w.1,e.symm w.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (g.cutoff nu)
    exact (hNormal (g.normal nu) (data.Omega nu) Sold (data.hOmega nu) (data.hSOmega nu)
      (data.hNormalobs nu) (j+1) ell Bnd (data.htau.trans_le data.htaul) data.hell1 hBnd
      (data.hNormalobsb nu) k hk z hz (hOld nu z hz ha)).trans hN
  refine ⟨{
    prim := data.prim
    primbar := data.prim
    hO := domains.1
    hSO := hRS
    hkappaO := domains.2.1
    hmapWO := domains.2.2.1
    Omega := Omega
    U := U
    Sloc := data.Sloc
    hOmega := fun nu => (domains.2.2.2.1 nu).1
    hSOmega := fun nu => (domains.2.2.2.1 nu).2.1
    hkappa := fun nu => (domains.2.2.2.1 nu).2.2.1
    hmapW := fun nu z hz => (hMapOm nu hz).1
    hU := fun nu beta => (domains.2.2.2.2 nu beta).1
    hOU := fun nu beta => (domains.2.2.2.2 nu beta).2.1
    hSloc := data.hSloc
    hsource := fun nu beta => (domains.2.2.2.2 nu beta).2.2.1
    hphi := fun nu beta => (domains.2.2.2.2 nu beta).2.2.2.1
    hmap := ?_
    htau := data.htau
    htaul := data.htaul
    hell1 := data.hell1
    hDelta := le_rfl
    L := data.L
    A := data.A
    Abar := data.Abar
    hL := data.hL
    hInput := data.hInput
    hInputbar := data.hInputbar
    hRep := data.hRep
    hRepbar := data.hRepbar
    hCut := data.hCut
    hEta := data.hEta
    hNormal := data.hNormal
    hBR := data.hBR
    hReserve := data.hReserve
    hBRb := fun nu beta k hk z hz => (data.hBRb nu beta k hk z hz).trans hB
    hLb := fun nu beta k hk z hz => (data.hLb nu beta k hk z hz).trans hB
    hInputb := fun nu beta k hk z hz => (data.hInputb nu beta k hk z hz).trans hB
    hInputbarb := fun nu beta k hk z hz => (data.hInputbarb nu beta k hk z hz).trans hB
    hCutb := fun nu beta k hk z hz => (data.hCutb nu beta k hk z hz).trans hB
    hEtab := fun nu beta k hk z hz => (data.hEtab nu beta k hk z hz).trans hB
    hNormalb := fun nu beta k hk z hz => (data.hNormalb nu beta k hk z hz).trans hB
    hDiff := data.hDiff
    hAb := data.hAb
    hBb := data.hBb
    hGb := data.hGb
    hJb := data.hJb
    hTb := data.hTb
    hphib := fun nu beta k hk1 hk z hz => hChart n length j Rsub Lprimary reserve Bnd Mg
      Tbackground hTbackground F hF g input input W primary O S tau ell 0 data hSample
      nu beta k hk1 hk z hz.1.1 hz.1.2 hz.2
    hRsub := ?_
    Lobs := fun _ _ => ContinuousLinearMap.id ℝ ℝ
    Aobs := arg
    Abarobs := arg
    hLobs := fun _ => contDiffOn_const
    hAobs := hArgSmooth
    hAbarobs := hArgSmooth
    hRepobs := fun _ _ _ => rfl
    hRepbarobs := fun _ _ _ => rfl
    hCutobs := hCutSmooth
    hNormalobs := hNormalSmooth
    hPhaseobs := hPhaseSmooth
    hReserveobs := ?_
    hLobsb := fun _ k _ z _ => hId k z
    hAobsb := fun nu k hk z hz => hArgs nu k hk z hz.1 hz.2
    hAbarobsb := fun nu k hk z hz => hArgs nu k hk z hz.1 hz.2
    hCutobsb := fun nu k hk z hz => hCuts nu k hk z hz.1 hz.2
    hNormalobsb := fun nu k hk z hz => hNormals nu k hk z hz.1 hz.2
    hGradobsb := fun nu r k hk z hz => (hGrad nu r k hk z hz.1 hz.2).trans hP
    hDiffobs := by intro nu k hk z hz; simp
    hCover := fun nu z hz => ⟨hz.1,data.prim.hPrimarySupport nu hz.2⟩
    hPositiveCover := fun nu z hz => ⟨data.prim.hPositive nu _ hz.2,data.prim.hPositive nu _ hz.2⟩
    hCount := ?_ }⟩
  · intro nu beta z hz
    have hzOld := hOld nu z hz.1.1 hz.1.2
    have haOld : ((phi z).1,e.symm (phi z).2) ∈ incrementsGlobalRelativeSupport W
        (fun w => g.eta nu beta w*g.cutoff nu w) := by
      rw [hpoint z hz.1.1]
      exact hz.2
    have hm := data.hmap nu beta ⟨hzOld,haOld⟩
    change g.chart nu beta ((phi z).1,e.symm (phi z).2) ∈ data.Sloc nu beta at hm
    rw [hpoint z hz.1.1] at hm
    exact hm
  · intro nu z hz
    have hb := data.hRsub nu (phi z) (hOld nu z hz.1 hz.2)
    dsimp only at hb
    simpa only [hpoint z hz.1] using hb
  · intro nu z hz
    have hb := (data.hReserveobs nu (phi z) (hOld nu z hz.1 hz.2)).1
    rw [hArgEq nu z hz.1 hz.2] at hb
    exact ⟨hb,hb⟩
  · intro z hz
    have hb := data.hCount (phi z) (hSample hz)
    simpa only [hpoint z hz] using hb

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_raw_rehost_uniform
