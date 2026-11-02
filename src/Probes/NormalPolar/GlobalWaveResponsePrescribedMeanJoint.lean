import Probes.Round4PrescribedNativeObservation
import Probes.ActualSpatialJointJets

/-! The complete native opposite mean is jointly smooth with phases smooth
only on their genuine active opens. Outside a relative closed carrier, both
actual amplitude germs vanish, so their native spatial coefficients vanish
before the quadratic mean is formed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold Filter GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem globalWave_native_coefficient_zero_of_amplitude_germs
    (phase : Ep × M → ℝ) (R Q : Ep × M → V) (tau : ℝ) (z : Ep × M)
    (hR : R =ᶠ[𝓝 z] 0) (hQ : Q =ᶠ[𝓝 z] 0) (ch : Bool) :
    round4PrescribedNativeCoefficient (I:=I) ch phase tau R Q z = 0 := by
  have hd (f : Ep × M → V) (hf : f =ᶠ[𝓝 z] 0) :
      incrementsGlobalSpatialDerivative (I:=I) f z = 0 := by
    have hs : (fun x : M => f (z.1,x)) =ᶠ[𝓝 z.2] 0 :=
      hf.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
    have he := hs.mfderiv_eq (I:=I) (I':=𝓘(ℝ,V))
    rw [show (0 : M → V) = (fun _ => (0 : V)) from rfl,mfderiv_const] at he
    unfold incrementsGlobalSpatialDerivative
    rw [he]
    ext v
    rfl
  cases ch <;> simp only [round4PrescribedNativeCoefficient,Bool.false_eq_true,ite_false,ite_true,
    hd R hR,hd Q hQ,hR.eq_of_nhds,hQ.eq_of_nhds,Pi.zero_apply,smul_zero,ContinuousLinearMap.smulRight_zero,
    sub_zero,add_zero]

theorem globalWave_native_opposite_mean_local_phase_joint
    (phase : Fin r → Ep × M → ℝ) (R Q : Fin r → Ep × M → V) (tau : ℝ)
    (W : Set (Ep × M)) (hW : IsOpen W) (K primary : Fin r → Set (Ep × M))
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W))
    (hprimary : ∀ l, IsOpen (primary l)) (hKprimary : ∀ l, K l ⊆ primary l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phase l) (W ∩ primary l))
    (hR : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞ (R l) W)
    (hQ : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞ (Q l) W)
    (hzero : ∀ l z, z ∈ W → z ∉ K l → R l z = 0 ∧ Q l z = 0)
    (obs : D → M) (O : Set X) (hO : IsOpen O)
    (hObs : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod I) ∞ (fun z : X => (z.1,obs z.2)) O)
    (hObsSlice : ∀ z ∈ O, ContMDiffAt 𝓘(ℝ,D) I ∞ obs z.2)
    (hMaps : MapsTo (fun z : X => (z.1,obs z.2)) O W) (v w : D) :
    ContDiffOn ℝ ∞ (fun z : X => round4NativeOppositeMean (I:=I) phase tau R Q z.1 (obs z.2)
      (mfderiv 𝓘(ℝ,D) I obs z.2 ((tangentSpaceCastModel 𝓘(ℝ,D) z.2).symm v))
      (mfderiv 𝓘(ℝ,D) I obs z.2 ((tangentSpaceCastModel 𝓘(ℝ,D) z.2).symm w))) O := by
  let kappa : X → Ep × M := fun z => (z.1,obs z.2)
  let A := fun (ch : Bool) l => if ch then Q l else R l
  have hA (ch : Bool) (l : Fin r) : ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞ (A ch l) W := by
    cases ch
    · exact hR l
    · exact hQ l
  let coeff := fun ch l q (z : X) => round4PrescribedNativeCoefficient (I:=I) ch (phase l) tau (R l) (Q l)
    (kappa z) (mfderiv 𝓘(ℝ,D) I obs z.2 ((tangentSpaceCastModel 𝓘(ℝ,D) z.2).symm q))
  have hcoeff (ch : Bool) (l : Fin r) (q : D) : ContDiffOn ℝ ∞ (coeff ch l q) O := by
    intro z hz
    by_cases hk : kappa z ∈ K l
    · let Oa := O ∩ kappa ⁻¹' primary l
      have hOa : IsOpen Oa := hObs.continuousOn.isOpen_inter_preimage hO (hprimary l)
      have hza : z ∈ Oa := ⟨hz,hKprimary l hk⟩
      let amps := fun (ch : Bool) (y : X) => A ch l (kappa y)
      let ph := fun y : X => phase l (kappa y)
      have hamps (c : Bool) : ContDiffOn ℝ ∞ (amps c) Oa :=
        (((hA c l).comp hObs hMaps).mono inter_subset_left).contDiffOn
      have hph : ContDiffOn ℝ ∞ ph Oa :=
        ((hphase l).comp (hObs.mono inter_subset_left) (fun y hy => ⟨hMaps hy.1,hy.2⟩)).contDiffOn
      let slow := fun y : X => fderiv ℝ (fun x => amps ch (y.1,x)) y.2 q
      let fast := fun y : X => fderiv ℝ (fun x => ph (y.1,x)) y.2 q • (tau⁻¹ • amps (!ch) y)
      have hs : ContDiffOn ℝ ∞ slow Oa :=
        ((incrementsJointSpatialJets_bridge (amps ch) Oa hOa (hamps ch)).2.1).clm_apply contDiffOn_const
      have hf : ContDiffOn ℝ ∞ fast Oa :=
        (((incrementsJointSpatialJets_bridge ph Oa hOa hph).2.1).clm_apply contDiffOn_const).smul
          ((hamps (!ch)).const_smul tau⁻¹)
      have hc : ContDiffOn ℝ ∞ (fun y => if ch then slow y+fast y else slow y-fast y) Oa := by
        cases ch
        · exact hs.sub hf
        · exact hs.add hf
      have he : EqOn (coeff ch l q) (fun y => if ch then slow y+fast y else slow y-fast y) Oa := by
        intro y hy
        have ha := round4_native_observation_derivative (A ch l) y.1 obs y.2 q
          ((hA ch l).contMDiffAt (hW.mem_nhds (hMaps hy.1))) (hObsSlice y hy.1)
        have hp := round4_native_observation_derivative (phase l) y.1 obs y.2 q
          ((hphase l).contMDiffAt ((hW.inter (hprimary l)).mem_nhds ⟨hMaps hy.1,hy.2⟩))
          (hObsSlice y hy.1)
        cases ch <;>
          simp only [coeff,round4PrescribedNativeCoefficient,Bool.false_eq_true,ite_false,ite_true,
            ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.smulRight_apply,
            slow,fast,amps,ph,A,kappa,Bool.not_false,Bool.not_true,
            incrementsGlobalSpatialDerivative,incrementsGlobalScalarDerivative,
            ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe] at * <;>
          rw [ha,hp] <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      exact ((hc.congr he).contDiffAt (hOa.mem_nhds hza)).contDiffWithinAt
    · let Vout : Set (Ep × M) := Subtype.val '' (Subtype.val ⁻¹' K l : Set W)ᶜ
      have hV : IsOpen Vout := hW.isOpenMap_subtype_val _ (hK l).isOpen_compl
      have hzV : kappa z ∈ Vout := ⟨⟨kappa z,hMaps hz⟩,hk,rfl⟩
      apply ContDiffAt.contDiffWithinAt
      apply (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
      have hkappa : ContinuousAt kappa z := hObs.continuousOn.continuousAt (hO.mem_nhds hz)
      filter_upwards [hO.mem_nhds hz,hkappa.eventually (hV.mem_nhds hzV)] with y hy hyV
      have hzG : ∀ c : Bool, A c l =ᶠ[𝓝 (kappa y)] 0 := by
        intro c
        filter_upwards [hV.mem_nhds hyV] with q hq
        obtain ⟨qq,hqK,he⟩ := hq
        have hzQ := hzero l q (he ▸ qq.property) (he ▸ hqK)
        cases c
        · exact hzQ.1
        · exact hzQ.2
      have hc := globalWave_native_coefficient_zero_of_amplitude_germs (I:=I) (phase l) (R l) (Q l)
        tau (kappa y) (hzG false) (hzG true) ch
      change round4PrescribedNativeCoefficient (I:=I) ch (phase l) tau (R l) (Q l) (kappa y) _ = 0
      rw [hc,ContinuousLinearMap.zero_apply]
  have hsum : ContDiffOn ℝ ∞ (fun z : X => (1/2 : ℝ)*∑ l,
      (inner ℝ (coeff false l v z) (coeff false l w z)+
        inner ℝ (coeff true l v z) (coeff true l w z))) O := by
    apply contDiffOn_const.mul
    apply ContDiffOn.sum
    intro l _
    exact ((hcoeff false l v).inner ℝ (hcoeff false l w)).add ((hcoeff true l v).inner ℝ (hcoeff true l w))
  convert hsum using 1
  funext z
  simp only [round4NativeOppositeMean,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.add_apply,
    LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,innerₗ_apply_apply,smul_eq_mul,coeff,kappa]

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_native_opposite_mean_local_phase_joint
