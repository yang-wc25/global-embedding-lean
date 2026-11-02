import Probes.ActualSecondaryPrimaryRawConsumers
import Smoothing.ParameterRound2MeanRawProfiles
import Smoothing.ParameterRound2PrimaryPhysicalIndex

/-! The primary displacement and linearized metric error needed by the actual
secondary construction are produced from the SAME raw profiles used by the
mean iteration. No U1 or primary-error output budget is supplied. The only
additional geometric data are genuine sliced charts, original admissibility,
free-normal membership and literal adaptation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M Tr Label Sub : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

private local instance primaryRawTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance primaryRawTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance primaryRawTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace

 theorem parameterRound2_original_primary_consumers_from_raw_index
    (n length j Rsub Lprimary : ℕ) (horder : j+2+length ≤ n)
    (c Bnd Mg : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    ∃ CU CP : ℝ, 0 ≤ CU ∧ 0 ≤ CP ∧ ∀ {Label Sub : Type*} [Fintype Label] [Fintype Sub]
      (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := Sub) F)
      (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (Ep × M)) (primary : Label → Set (Ep × M))
      (e : OpenPartialHomeomorph M D) (O S : Set X) (tau ell Delta : ℝ)
      (raw : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary c Bnd Mg T
        F hF g input inputbar W primary e O S tau ell Delta)
      (geom : ActualOriginalPrimaryPhysicalGeometry F hF g) (delta : ℝ),
    let kappa := fun z : X => (z.1,e.symm z.2)
    let Fobs := fun z : X => F z.1 (e.symm z.2)
    let U := fun z : X => delta • incrementsGlobalPrimaryWave F hF g input length tau (kappa z)
    ContDiffOn ℝ ∞ U O ∧ ContDiffOn ℝ ∞ (actualJointMetricLinearization Fobs U) O ∧
      (∀ r ≤ j+1, ∀ z ∈ S, tau^r*‖iteratedFDeriv ℝ r U z‖ ≤ CU*|delta| *tau) ∧
      (∀ r ≤ j, ∀ z ∈ S, tau^r*‖iteratedFDeriv ℝ r (actualJointMetricLinearization Fobs U) z‖ ≤
        CP*|delta| *tau*(tau/ell)^length) := by
  let Mgeom := max Mg Bnd
  have hM : 0 ≤ Mgeom := hMg.trans (le_max_left _ _)
  obtain ⟨CU,hCU,hWave⟩ := parameterRound2_original_primary_wave_jets_uniform_index
    (I := 𝓙) (M := M) (Ep := Ep) (Y := X) (T0 := Tr) (m := m) (N := N)
    n length (j+1) Lprimary Rsub (by omega) c Bnd Mgeom hc hBnd hM T hT
  obtain ⟨CP,hCP,hPhysical⟩ := parameterRound2_original_primary_physical_jets_uniform_index
    (M := M) (Ep := Ep) (Eq := Ep) (T0 := Tr) (m := m) (N := N)
    n length j Lprimary Rsub (by omega) c Bnd Mgeom hc hBnd hM T hT
  refine ⟨CU,CP,hCU,hCP,?_⟩
  intro Label Sub _ _ F hF g input inputbar W primary e O S tau ell Delta raw geom delta kappa Fobs U
  let h := raw.prim
  let Ks := fun nu beta => incrementsGlobalRelativeSupport W (fun z => g.eta nu beta z*g.cutoff nu z)
  let Kp := fun nu => incrementsGlobalRelativeSupport W (g.cutoff nu)
  let OO := fun nu beta => O ∩ raw.Omega nu ∩ raw.U nu beta
  have hsub : ∀ nu beta, Ks nu beta ⊆ Kp nu := by
    intro nu beta
    dsimp only [Ks,Kp]
    rw [parameterRound2_global_relativeSupport_eq W h.hW,parameterRound2_global_relativeSupport_eq W h.hW]
    exact Set.inter_subset_inter_right W tsupport_mul_subset_right
  have hOO : ∀ nu beta, IsOpen (OO nu beta) :=
    fun nu beta => (raw.hO.inter (raw.hOmega nu)).inter (raw.hU nu beta)
  have hactive : ∀ nu beta, O ∩ kappa ⁻¹' Ks nu beta ⊆ OO nu beta := by
    intro nu beta z hz
    have hp := raw.hCover nu ⟨hz.1,hsub nu beta hz.2⟩
    exact ⟨⟨hz.1,hp⟩,raw.hOU nu beta ⟨hp,hz.2⟩⟩
  have hsource : ∀ nu beta, MapsTo kappa (OO nu beta) (g.chart nu beta).source :=
    fun nu beta z hz => raw.hsource nu beta hz.2
  have htrans : ∀ nu beta, ContDiffOn ℝ ∞ (g.chart nu beta ∘ kappa) (OO nu beta) :=
    fun nu beta => (raw.hphi nu beta).mono inter_subset_right
  have hadapt : ∀ nu beta z, z ∈ OO nu beta → g.phase nu (kappa z) = (g.chart nu beta (kappa z)).2 0 :=
    fun nu beta z hz => geom.adaptation nu beta _ (hsource nu beta hz)
  have hsample : ∀ nu beta z, z ∈ S ∩ kappa ⁻¹' Ks nu beta → g.chart nu beta (kappa z) ∈ raw.Sloc nu beta :=
    fun nu beta z hz => raw.hmap nu beta ⟨⟨hz.1,hsub nu beta hz.2⟩,hz.2⟩
  have htransb : ∀ nu beta z, z ∈ S ∩ kappa ⁻¹' Ks nu beta → ∀ k, 1 ≤ k → k ≤ j+1 →
      ell^(k-1)*‖iteratedFDeriv ℝ k (g.chart nu beta ∘ kappa) z‖ ≤ T k :=
    fun nu beta z hz k hk hj => raw.hphib nu beta k hk hj z ⟨⟨hz.1,hsub nu beta hz.2⟩,hz.2⟩
  have hRsub : ∀ nu z, z ∈ S → (Finset.univ.filter (fun beta => kappa z ∈ Ks nu beta)).card ≤ Rsub := by
    intro nu z hz
    by_cases hp : kappa z ∈ Kp nu
    · exact raw.hRsub nu z ⟨hz,hp⟩
    · have hempty : Finset.univ.filter (fun beta => kappa z ∈ Ks nu beta) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro beta hb
        exact hp (hsub nu beta (Finset.mem_filter.mp hb).2)
      rw [hempty,Finset.card_empty]
      exact Nat.zero_le _
  have hSecondb := fun nu beta k hk z hz => (raw.hBRb nu beta k hk z hz).trans (le_max_right Mg Bnd)
  have hAb := fun nu beta k hk z hz => (raw.hAb nu beta k hk z hz).trans (le_max_left Mg Bnd)
  have hBb := fun nu beta k hk z hz => (raw.hBb nu beta k hk z hz).trans (le_max_left Mg Bnd)
  have hGb := fun nu beta k hk z hz => (raw.hGb nu beta k hk z hz).trans (le_max_left Mg Bnd)
  have hJb := fun nu beta k hk z hz => (raw.hJb nu beta k hk z hz).trans (le_max_left Mg Bnd)
  have hTb := fun nu beta k hk z hz => (raw.hTb nu beta k hk z hz).trans (le_max_left Mg Bnd)
  have hw := hWave F hF g input tau ell raw.htau raw.htaul raw.hell1 W h.hW primary h.hPrimary
    h.hPrimarySupport h.hSourceW h.hChart h.hChartInv h.hInverse h.hCombinedSupport h.hCut h.hNormal
    h.hArgument h.hEta h.hPositive h.hG h.hJ h.hT0 h.hA h.hB h.hSecond raw.Sloc raw.hSloc
    raw.L raw.A raw.hL raw.hInput raw.hRep (fun nu beta z hz => (raw.hReserve nu beta z hz).1)
    raw.hLb raw.hInputb raw.hCutb raw.hEtab raw.hNormalb hAb hBb hGb hJb hTb hSecondb
    kappa O S raw.hO raw.hSO raw.hkappaO raw.hmapWO OO hOO hactive hsource hadapt htrans
    hsample htransb raw.hCount hRsub
  have hp := hPhysical F hF g input tau ell raw.htau raw.htaul raw.hell1 W h.hW primary h.hPrimary
    h.hPrimarySupport h.hSourceW h.hChart h.hChartInv h.hInverse h.hCombinedSupport h.hCut h.hNormal
    h.hArgument h.hEta h.hPositive h.hG h.hJ h.hT0 h.hA h.hB h.hSecond
    geom.slices geom.maximal geom.inverse geom.target geom.immersion geom.gram geom.normalKernel
    raw.Sloc raw.hSloc raw.L raw.A raw.hL raw.hInput raw.hRep
    (fun nu beta z hz => (raw.hReserve nu beta z hz).1) raw.hLb raw.hInputb raw.hCutb raw.hEtab raw.hNormalb
    hAb hBb hSecondb kappa id (fun _ => rfl) O S raw.hO raw.hSO raw.hkappaO raw.hmapWO
    OO hOO hactive hsource hadapt htrans hsample htransb raw.hCount hRsub
  let U0 := incrementsGlobalPrimaryWave F hF g input length tau ∘ kappa
  have heq : EqOn (actualJointMetricLinearization Fobs U)
      (fun z => delta • actualJointMetricLinearization Fobs U0 z) O := by
    intro z hz
    have hd := (actual_joint_contDiffOn_slice U0 O hw.1 z.1).contDiffAt
      ((raw.hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)
    change actualJointMetricLinearization Fobs (fun y => delta • U0 y) z =
      delta • actualJointMetricLinearization Fobs U0 z
    ext v w
    simp only [actualJointMetricLinearization,actualCoordinateMetricLinearization_apply,
      fderiv_fun_const_smul (hd.differentiableAt (by simp)) delta,
      ContinuousLinearMap.smul_apply,inner_smul_right,real_inner_smul_left]
    ring
  refine ⟨hw.1.const_smul delta,(hp.2.1.const_smul delta).congr heq,hw.2 delta,?_⟩
  intro r hr z hz
  exact (hp.2.2 delta r hr z hz).trans_eq (by ring)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.parameterRound2_original_primary_consumers_from_raw_index
