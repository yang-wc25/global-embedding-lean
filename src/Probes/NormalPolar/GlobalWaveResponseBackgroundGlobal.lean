import NormalPolar.GlobalWaveResponseBackgroundLocal
import Probes.ActualIncrementPrimaryObservation

/-! The actual complete global background wave obeys a two-point fast-jet
bound on every raw observer sample. Both support boundaries and active
primary/subordinate counts are treated by the actual supported-sum theorem.
The only extra identity is the genuine adapted chart phase identity, which
is not stored in the raw mean profile record. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation
variable {E H M Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep×D

theorem globalWave_background_global_raw_difference
    (n length j Rsub Lprimary : ℕ) (horder : j+1+length ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β]
      (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I:=I) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
      (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (W : Set (Ep×M)) (primary : Λ → Set (Ep×M))
      (e : OpenPartialHomeomorph M D) (O S : Set X) (tau ell Delta : ℝ)
      (raw : ParameterRound2GlobalMeanRawProfiles (Tr:=Tr) n length j Rsub Lprimary reserve Bnd Mg T
        F hF g input inputbar W primary e O S tau ell Delta)
      (hadapt : ∀ nu beta y, y ∈ raw.U nu beta →
        g.phase nu (y.1,e.symm y.2) = (g.chart nu beta (y.1,e.symm y.2)).2 0),
    let A := fun y : X => incrementsGlobalPrimaryWave F hF g input length tau (y.1,e.symm y.2)
    let B := fun y : X => incrementsGlobalPrimaryWave F hF g inputbar length tau (y.1,e.symm y.2)
    ContDiffOn ℝ ∞ (fun y => A y-B y) O ∧
      ∀ k ≤ j, ∀ y ∈ S, tau^k*‖iteratedFDeriv ℝ k (fun z => A z-B z) y‖ ≤ C*tau*Delta := by
  obtain ⟨Cw,hCw,hlocal⟩ := globalWave_background_local_raw_difference
    (I:=I) (M:=M) (Ep:=Ep) (Tr:=Tr) (m:=m) (N:=N) n length j horder reserve Bnd Mg hc hBnd hMg
  let Ct := actualFastChartTransferPrefix T j
  have hCt : 0 ≤ Ct := actualFastChartTransferPrefix_nonneg T hT j
  refine ⟨(Lprimary*Rsub : ℕ)*Ct*Cw,by positivity,?_⟩
  intro Λ Β _ _ F hF g input inputbar W primary e O S tau ell Delta raw hadapt A B
  have htau := raw.htau
  have hDelta := raw.hDelta
  let kappa : X → Ep×M := fun y => (y.1,e.symm y.2)
  let Kp := fun nu => incrementsGlobalRelativeSupport W (g.cutoff nu)
  let Ks := fun nu beta => incrementsGlobalRelativeSupport W (fun z => g.eta nu beta z*g.cutoff nu z)
  have hsub : ∀ nu beta, Ks nu beta ⊆ Kp nu := by
    intro nu beta
    dsimp only [Ks,Kp]
    rw [parameterRound2_global_relativeSupport_eq W raw.prim.hW,
      parameterRound2_global_relativeSupport_eq W raw.prim.hW]
    exact Set.inter_subset_inter_right W tsupport_mul_subset_right
  let piece := fun (v : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) nu beta y =>
    Real.cos (g.phase nu y/tau) • incrementsGlobalPrimaryExtension F hF g v length tau true nu beta y-
      Real.sin (g.phase nu y/tau) • incrementsGlobalPrimaryExtension F hF g v length tau false nu beta y
  let pieces := fun nu beta y => piece input nu beta y-piece inputbar nu beta y
  have hreg0 (v : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (hp : ParameterRound2GlobalMeanPrimitives F hF g v W primary) :=
    actual_global_primary_extension_regular F hF g v length tau W hp.hW primary hp.hPrimary
      hp.hPrimarySupport hp.hSourceW hp.hChart hp.hChartInv hp.hInverse hp.hCombinedSupport
      hp.hCut hp.hNormal hp.hArgument hp.hEta hp.hPositive hp.hG hp.hJ hp.hT0 hp.hA hp.hB hp.hSecond
  have hpieceZero (v : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (hp : ParameterRound2GlobalMeanPrimitives F hF g v W primary)
      (nu : Λ) (beta : Β) (z : W) (hn : z.val ∉ Ks nu beta) : piece v nu beta z = 0 := by
    have hr : incrementsGlobalPrimaryExtension F hF g v length tau true nu beta z = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun w : W =>
        incrementsGlobalPrimaryExtension F hF g v length tau true nu beta w)
        (fun h => hn ((hreg0 v hp nu beta).2.2.2.2.1 h))
    have hi : incrementsGlobalPrimaryExtension F hF g v length tau false nu beta z = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun w : W =>
        incrementsGlobalPrimaryExtension F hF g v length tau false nu beta w)
        (fun h => hn ((hreg0 v hp nu beta).2.2.2.2.2 h))
    simp only [piece,hr,hi,smul_zero,sub_zero]
  have hsupport : ∀ nu beta, tsupport (fun y : W => pieces nu beta y) ⊆ Subtype.val ⁻¹' Ks nu beta := by
    intro nu beta
    have hKs : IsClosed (Subtype.val ⁻¹' Ks nu beta : Set W) := by
      dsimp only [Ks]
      rw [parameterRound2_global_relativeSupport_eq W raw.prim.hW]
      simpa only [Set.preimage_inter,Subtype.coe_preimage_self,Set.univ_inter] using
        (isClosed_tsupport (fun z => g.eta nu beta z*g.cutoff nu z)).preimage continuous_subtype_val
    apply closure_minimal _ hKs
    intro z hz
    by_contra hn
    apply hz
    simp only [pieces,hpieceZero input raw.prim nu beta z hn,
      hpieceZero inputbar raw.primbar nu beta z hn,sub_self]
  let localD := fun nu beta z => globalWaveBackgroundLocal F hF g input length tau nu beta z-
    globalWaveBackgroundLocal F hF g inputbar length tau nu beta z
  have hl (nu : Λ) (beta : Β) := hlocal F hF g input inputbar W primary e O S
    Rsub Lprimary T tau ell Delta raw nu beta
  have hactive : ∀ nu beta, O ∩ kappa ⁻¹' Ks nu beta ⊆ raw.U nu beta := by
    intro nu beta y hy
    exact raw.hOU nu beta ⟨raw.hCover nu ⟨hy.1,hsub nu beta hy.2⟩,hy.2⟩
  have he (nu : Λ) (beta : Β) : EqOn (pieces nu beta ∘ kappa)
      (localD nu beta ∘ (g.chart nu beta ∘ kappa)) (raw.U nu beta) := by
    intro y hy
    simp only [pieces,piece,localD,kappa,globalWaveBackgroundLocal,actualSecondaryModulation,
      Function.comp_def,incrementsGlobalPrimaryExtension,if_pos (raw.hsource nu beta hy),hadapt nu beta y hy]
  have hmap (nu : Λ) (beta : Β) : MapsTo (g.chart nu beta ∘ kappa) (raw.U nu beta)
      (g.chart nu beta).target := fun y hy => (g.chart nu beta).map_source (raw.hsource nu beta hy)
  have hreg : ∀ nu beta, ContDiffOn ℝ ∞ (pieces nu beta ∘ kappa) (raw.U nu beta) := by
    intro nu beta
    exact ((hl nu beta).1.comp (raw.hphi nu beta) (hmap nu beta)).congr (he nu beta)
  have hbound : ∀ nu beta, ∀ k ≤ j, ∀ y ∈ S ∩ kappa ⁻¹' Ks nu beta,
      tau^k*‖iteratedFDeriv ℝ k (pieces nu beta ∘ kappa) y‖ ≤ Ct*Cw*tau*Delta := by
    intro nu beta k hk y hy
    have hy' : y ∈ (S ∩ kappa ⁻¹' Kp nu) ∩ kappa ⁻¹' Ks nu beta :=
      ⟨⟨hy.1,hsub nu beta hy.2⟩,hy.2⟩
    have hyU := hactive nu beta ⟨raw.hSO hy.1,hy.2⟩
    have hnear := (he nu beta).eventuallyEq_of_mem ((raw.hU nu beta).mem_nhds hyU)
    rw [(hnear.iteratedFDeriv ℝ k).eq_of_nhds]
    have hb := actual_fast_joint_chart_transfer T hT k (g.chart nu beta ∘ kappa) (localD nu beta)
      (raw.U nu beta) (g.chart nu beta).target (raw.hU nu beta) (g.chart nu beta).open_target
      (raw.hphi nu beta) (hl nu beta).1 (hmap nu beta) y hyU tau ell (Cw*tau*Delta)
      raw.htau raw.htaul (fun a ha => (hl nu beta).2 a (ha.trans hk) _ (raw.hmap nu beta hy'))
      (fun a ha hak => raw.hphib nu beta a ha (by omega) y hy')
    exact hb.trans ((mul_le_mul_of_nonneg_right (actualFastChartTransferCost_le_prefix T hT hk)
      (by positivity : 0 ≤ Cw*tau*Delta)).trans_eq (by ring))
  have hRsub : ∀ nu y, y ∈ S → (Finset.univ.filter (fun beta => kappa y ∈ Ks nu beta)).card ≤ Rsub := by
    intro nu y hy
    by_cases hp : kappa y ∈ Kp nu
    · exact raw.hRsub nu y ⟨hy,hp⟩
    · have he0 : (Finset.univ.filter (fun beta => kappa y ∈ Ks nu beta)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro beta hb
        exact hp (hsub nu beta (Finset.mem_filter.mp hb).2)
      rw [he0,Finset.card_empty]
      exact Nat.zero_le _
  have hsum := actual_primary_observation_sum_weighted_jets pieces Kp Ks hsub W raw.prim.hW
    hsupport kappa O S raw.hO raw.hSO raw.hkappaO raw.hmapWO raw.U raw.hU hactive hreg
    Lprimary Rsub j raw.hCount hRsub tau (Ct*Cw*tau*Delta) raw.htau (by positivity) hbound
  have hactual : (fun y => A y-B y) = fun y => ∑ nu, ∑ beta, pieces nu beta (kappa y) := by
    funext y
    dsimp only [A,B]
    rw [actual_original_primary_wave_eq_piece_sum F hF g input length tau,
      actual_original_primary_wave_eq_piece_sum F hF g inputbar length tau]
    simp only [pieces,piece,kappa,Finset.sum_sub_distrib]
  rw [← hactual] at hsum
  refine ⟨hsum.1,?_⟩
  intro k hk y hy
  exact (hsum.2 k hk y hy).trans_eq (by ring)

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_background_global_raw_difference
