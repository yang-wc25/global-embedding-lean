import Probes.ActualIncrementJointDirectionalJets
import Probes.ActualJointHomogeneousParameter
import GlobalEmbedding.Paper.IncrementsFullNormalizedPrimaryError

/-! The literal normalized primary coefficient with all auxiliary derivatives.
Only source differentiation enters its formula; all norms below differentiate
jointly. Its free and actual reconstructed slow pieces keep the tau/ell gain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

/-- The fixed real bilinear phase product appearing in the original coefficient. -/
def actualJointPhaseProduct : ℝ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (Complex.I • ContinuousLinearMap.id ℝ ℂ)

theorem actualJointPhaseProduct_apply (a : ℝ) (z : ℂ) :
    actualJointPhaseProduct a z = Complex.I * (a : ℂ) * z := by
  change a • (Complex.I • z) = _
  simp only [Complex.real_smul,smul_eq_mul]
  ring

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def actualJointPrimaryErrorCost (j : ℕ) (v : D) (coord : Fin N) (Cv Cz Mphi : ℝ) : ℝ :=
  ‖incrementsFreeComplexCoordinate coord‖ * ‖ContinuousLinearMap.apply ℝ V v‖ * Cv +
    (‖ContinuousLinearMap.apply ℝ ℂ v‖ + 2^j * ‖actualJointPhaseProduct‖ * Mphi) * Cz

theorem actualJointPrimaryErrorCost_nonneg (j : ℕ) (v : D) (coord : Fin N)
    {Cv Cz Mphi : ℝ} (hv : 0 ≤ Cv) (hz : 0 ≤ Cz) (hp : 0 ≤ Mphi) :
    0 ≤ actualJointPrimaryErrorCost j v coord Cv Cz Mphi := by
  unfold actualJointPrimaryErrorCost
  positivity

/-- All joint jets of the actual normalized error. The intermediate free and
correction-sum budgets are supplied by the original positive-amplitude and actual
finite reconstruction producers; no error or mean estimate is assumed. -/
theorem actual_joint_primary_error_slow_jets {A : Type*} [Fintype A]
    (b phi : X → ℝ) (normal : X → V) (P Q : A → X → V)
    (v : D) (coord : Fin N) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hb : ContDiffOn ℝ ∞ b O) (hn : ContDiffOn ℝ ∞ normal O)
    (hphi : ContDiffOn ℝ ∞ phi O)
    (hP : ∀ a, ContDiffOn ℝ ∞ (P a) O) (hQ : ∀ a, ContDiffOn ℝ ∞ (Q a) O)
    (j : ℕ) (ell tau Cv Cz Mphi : ℝ) (hell : 0 < ell) (htau : 0 < tau)
    (htaul : tau ≤ ell) (hCv : 0 ≤ Cv) (hCz : 0 ≤ Cz) (hMphi : 0 ≤ Mphi) :
    let VF := fun z : X => (Real.sqrt 2 * 1 * tau * b z) • normal z
    let C := fun z : X => ∑ a, (incrementsFreeComplexCoordinate coord (P a z) +
      Complex.I • incrementsFreeComplexCoordinate coord (Q a z))
    let grad := fun z : X => fderiv ℝ (fun x => phi (z.1,x)) z.2 v
    let err := fun z : X => incrementsPrimaryErrorCoefficient 1 tau
      (fun x => b (z.1,x)) (fun x => phi (z.1,x)) (fun x => normal (z.1,x))
      (fun a x => P a (z.1,x)) (fun a x => Q a (z.1,x)) z.2 v coord
    (∀ k ≤ j+1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k VF z‖ ≤ Cv*tau) →
    (∀ k ≤ j+1, ∀ z ∈ S, ell^(k+1) * ‖iteratedFDeriv ℝ k C z‖ ≤ Cz*tau^2) →
    (∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k grad z‖ ≤ Mphi) →
    ContDiffOn ℝ ∞ err O ∧ ∀ k ≤ j, ∀ z ∈ S,
      ell^k * ‖iteratedFDeriv ℝ k err z‖ ≤
        actualJointPrimaryErrorCost j v coord Cv Cz Mphi * (tau/ell) := by
  intro VF C grad err hVb hCb hgradb
  let ev := incrementsFreeComplexCoordinate coord
  let dV := fun z : X => fderiv ℝ (fun x => VF (z.1,x)) z.2 v
  let dC := fun z : X => fderiv ℝ (fun x => C (z.1,x)) z.2 v
  let free := fun z : X => ev (dV z)
  let fast := fun z : X => tau⁻¹ • actualJointPhaseProduct (grad z) (C z)
  have hVF : ContDiffOn ℝ ∞ VF O :=
    (hb.const_smul (Real.sqrt 2 * 1 * tau)).smul hn
  have hC : ContDiffOn ℝ ∞ C O :=
    ContDiffOn.sum fun a _ => (ev.contDiff.comp_contDiffOn (hP a)).add
      ((ev.contDiff.comp_contDiffOn (hQ a)).const_smul Complex.I)
  have hgrad : ContDiffOn ℝ ∞ grad O :=
    ((incrementsJointSpatialJets_bridge phi O hO hphi).2.1).clm_apply contDiffOn_const
  obtain ⟨hdV,hdVb⟩ := actual_joint_directional_slow_jets VF v O S hO hSO hVF j ell
    (Cv*tau) hell hVb
  have hCb' : ∀ k ≤ j+1, ∀ z ∈ S,
      ell^k * ‖iteratedFDeriv ℝ k C z‖ ≤ Cz*tau^2/ell := by
    intro k hk z hz
    apply (le_div_iff₀ hell).mpr
    calc
      _ = ell^(k+1) * ‖iteratedFDeriv ℝ k C z‖ := by rw [pow_succ]; ring
      _ ≤ _ := hCb k hk z hz
  obtain ⟨hdC,hdCb⟩ := actual_joint_directional_slow_jets C v O S hO hSO hC j ell
    (Cz*tau^2/ell) hell hCb'
  have hfree : ContDiffOn ℝ ∞ free O := ev.contDiff.comp_contDiffOn hdV
  have hprod : ContDiffOn ℝ ∞ (fun z : X => actualJointPhaseProduct (grad z) (C z)) O :=
    (actualJointPhaseProduct.contDiff.comp_contDiffOn hgrad).clm_apply hC
  have hfast : ContDiffOn ℝ ∞ fast O := hprod.const_smul tau⁻¹
  have heq : EqOn err (fun z => free z+dC z+fast z) O := by
    intro z hz
    have hbs := (actual_joint_contDiffOn_slice b O hb z.1).contDiffAt
      ((hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)
    have hns := (actual_joint_contDiffOn_slice normal O hn z.1).contDiffAt
      ((hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)
    have hps (a : A) := (actual_joint_contDiffOn_slice (P a) O (hP a) z.1).contDiffAt
      ((hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)
    have hqs (a : A) := (actual_joint_contDiffOn_slice (Q a) O (hQ a) z.1).contDiffAt
      ((hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)
    have hh := increments_full_normalized_primary_error_eq tau (fun x => b (z.1,x))
      (fun x => phi (z.1,x)) (fun x => normal (z.1,x))
      (fun a x => P a (z.1,x)) (fun a x => Q a (z.1,x)) z.2 v coord
      (hbs.differentiableAt (by simp)) (hns.differentiableAt (by simp))
      (fun a => (hps a).differentiableAt (by simp))
      (fun a => (hqs a).differentiableAt (by simp))
    change err z = free z+dC z+Complex.I*((grad z : ℂ)/(tau : ℂ))*C z at hh
    rw [hh]
    congr 1
    rw [show fast z = tau⁻¹ • actualJointPhaseProduct (grad z) (C z) from rfl,
      actualJointPhaseProduct_apply, Complex.real_smul]
    push_cast
    ring
  refine ⟨((hfree.add hdC).add hfast).congr heq,?_⟩
  intro k hk z hz
  have hfreeb : ell^k * ‖iteratedFDeriv ℝ k free z‖ ≤
      ‖ev‖*‖ContinuousLinearMap.apply ℝ V v‖*Cv*(tau/ell) := by
    have hh := slow_linear_jet_bound ev O hO dV hdV k ell
      (‖ContinuousLinearMap.apply ℝ V v‖*(Cv*tau)/ell) hell.le z (hSO hz)
      (hdVb k hk z hz)
    exact hh.trans_eq (by ring)
  have hsq : (tau/ell)^2 ≤ tau/ell := by
    have h0 : 0 ≤ tau/ell := div_nonneg htau.le hell.le
    have h1 : tau/ell ≤ 1 := (div_le_one hell).mpr htaul
    nlinarith
  have hdCbound : ell^k * ‖iteratedFDeriv ℝ k dC z‖ ≤
      ‖ContinuousLinearMap.apply ℝ ℂ v‖*Cz*(tau/ell) := by
    calc
      _ ≤ ‖ContinuousLinearMap.apply ℝ ℂ v‖*(Cz*tau^2/ell)/ell := hdCb k hk z hz
      _ = (‖ContinuousLinearMap.apply ℝ ℂ v‖*Cz)*(tau/ell)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (mul_nonneg (ContinuousLinearMap.apply ℝ ℂ v).opNorm_nonneg hCz)
  have hprodBound := slow_bilinear_jet_bound_norm actualJointPhaseProduct O hO grad C
    hgrad hC k ell Mphi (Cz*tau^2/ell) hell.le z (hSO hz)
    (fun r hr => hgradb r (hr.trans hk) z hz)
    (fun r hr => hCb' r (by omega) z hz)
  have hfastb : ell^k * ‖iteratedFDeriv ℝ k fast z‖ ≤
      (2^j*‖actualJointPhaseProduct‖*Mphi*Cz)*(tau/ell) := by
    change ell^k * ‖iteratedFDeriv ℝ k
      (fun y => tau⁻¹ • actualJointPhaseProduct (grad y) (C y)) z‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hprod.contDiffAt (hO.mem_nhds (hSO hz))).of_le
      (by simp : (k : ℕ∞ω) ≤ ∞)),norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos htau]
    calc
      _ = tau⁻¹ * (ell^k * ‖iteratedFDeriv ℝ k
        (fun y => actualJointPhaseProduct (grad y) (C y)) z‖) := by ring
      _ ≤ tau⁻¹*(2^k*(‖actualJointPhaseProduct‖*Mphi)*(Cz*tau^2/ell)) :=
        mul_le_mul_of_nonneg_left hprodBound (inv_nonneg.mpr htau.le)
      _ = (2^k*‖actualJointPhaseProduct‖*Mphi*Cz)*(tau/ell) := by
        field_simp [htau.ne'] <;> ring
      _ ≤ _ := by gcongr; norm_num
  have hadd := actual_joint_slow_add_jet_bound free dC k ell _ _ hell.le z
    ((hfree.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp))
    ((hdC.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp)) hfreeb hdCbound
  have hall := actual_joint_slow_add_jet_bound (fun y => free y+dC y) fast k ell _ _ hell.le z
    (((hfree.add hdC).contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp))
    ((hfast.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp)) hadd hfastb
  have hg : err =ᶠ[𝓝 z] (fun y => free y+dC y+fast y) :=
    eventuallyEq_of_mem (hO.mem_nhds (hSO hz)) (fun y hy => heq hy)
  rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hall.trans_eq (by unfold actualJointPrimaryErrorCost; dsimp only [ev]; ring)

/-- The SAME-input normalized error difference retains exactly one tau/ell
factor. It is the original coefficient subtraction on actual smooth germs. -/
theorem actual_joint_primary_error_difference_slow_jets {A : Type*} [Fintype A]
    (b bbar phi : X → ℝ) (normal : X → V) (P Q Pbar Qbar : A → X → V)
    (v : D) (coord : Fin N) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hb : ContDiffOn ℝ ∞ b O) (hbbar : ContDiffOn ℝ ∞ bbar O)
    (hn : ContDiffOn ℝ ∞ normal O) (hphi : ContDiffOn ℝ ∞ phi O)
    (hP : ∀ a, ContDiffOn ℝ ∞ (P a) O) (hQ : ∀ a, ContDiffOn ℝ ∞ (Q a) O)
    (hPbar : ∀ a, ContDiffOn ℝ ∞ (Pbar a) O) (hQbar : ∀ a, ContDiffOn ℝ ∞ (Qbar a) O)
    (j : ℕ) (ell tau Cv Cz Mphi Delta : ℝ) (hell : 0 < ell) (htau : 0 < tau)
    (htaul : tau ≤ ell) (hCv : 0 ≤ Cv) (hCz : 0 ≤ Cz) (hMphi : 0 ≤ Mphi)
    (hDelta : 0 ≤ Delta) :
    let VF := fun (b : X → ℝ) (z : X) => (Real.sqrt 2 * 1 * tau * b z) • normal z
    let C := fun (P Q : A → X → V) (z : X) => ∑ a,
      (incrementsFreeComplexCoordinate coord (P a z) +
        Complex.I • incrementsFreeComplexCoordinate coord (Q a z))
    let grad := fun z : X => fderiv ℝ (fun x => phi (z.1,x)) z.2 v
    let err := fun (b : X → ℝ) (P Q : A → X → V) (z : X) =>
      incrementsPrimaryErrorCoefficient 1 tau
        (fun x => b (z.1,x)) (fun x => phi (z.1,x)) (fun x => normal (z.1,x))
        (fun a x => P a (z.1,x)) (fun a x => Q a (z.1,x)) z.2 v coord
    (∀ k ≤ j+1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w => VF b w-VF bbar w) z‖ ≤ Cv*tau*Delta) →
    (∀ k ≤ j+1, ∀ z ∈ S, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun w => C P Q w-C Pbar Qbar w) z‖ ≤ Cz*tau^2*Delta) →
    (∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k grad z‖ ≤ Mphi) →
    ContDiffOn ℝ ∞ (fun z => err b P Q z-err bbar Pbar Qbar z) O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
        (fun w => err b P Q w-err bbar Pbar Qbar w) z‖ ≤
          actualJointPrimaryErrorCost j v coord Cv Cz Mphi * (tau/ell) * Delta := by
  intro VF C grad err hVd hCd hgradb
  let bd := fun z => b z-bbar z
  let Pd := fun a z => P a z-Pbar a z
  let Qd := fun a z => Q a z-Qbar a z
  have hVeq : VF bd = fun z => VF b z-VF bbar z := by
    funext z
    simp only [VF,bd,mul_sub,sub_smul]
  have hCeq : C Pd Qd = fun z => C P Q z-C Pbar Qbar z := by
    funext z
    dsimp only [C,Pd,Qd]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [map_sub,smul_sub]
    abel
  have hVdb : ∀ k ≤ j+1, ∀ z ∈ S,
      ell^k * ‖iteratedFDeriv ℝ k (VF bd) z‖ ≤ (Cv*Delta)*tau := by
    rw [hVeq]
    intro k hk z hz
    exact (hVd k hk z hz).trans_eq (by ring)
  have hCdb : ∀ k ≤ j+1, ∀ z ∈ S,
      ell^(k+1) * ‖iteratedFDeriv ℝ k (C Pd Qd) z‖ ≤ (Cz*Delta)*tau^2 := by
    rw [hCeq]
    intro k hk z hz
    exact (hCd k hk z hz).trans_eq (by ring)
  obtain ⟨heSmooth,heBound⟩ := actual_joint_primary_error_slow_jets bd phi normal Pd Qd
    v coord O S hO hSO (hb.sub hbbar) hn hphi (fun a => (hP a).sub (hPbar a))
    (fun a => (hQ a).sub (hQbar a)) j ell tau (Cv*Delta) (Cz*Delta) Mphi hell htau
    htaul (mul_nonneg hCv hDelta) (mul_nonneg hCz hDelta) hMphi hVdb hCdb hgradb
  have heq : EqOn (fun z => err b P Q z-err bbar Pbar Qbar z) (err bd Pd Qd) O := by
    intro z hz
    let Os : Set D := (fun x : D => (z.1,x)) ⁻¹' O
    have hOs : IsOpen Os := hO.preimage (continuous_const.prodMk continuous_id)
    exact increments_full_normalized_primary_error_sub
      (fun x => b (z.1,x)) (fun x => bbar (z.1,x)) (fun x => phi (z.1,x))
      (fun x => normal (z.1,x)) (fun a x => P a (z.1,x)) (fun a x => Q a (z.1,x))
      (fun a x => Pbar a (z.1,x)) (fun a x => Qbar a (z.1,x)) tau v coord Os hOs
      (actual_joint_contDiffOn_slice b O hb z.1) (actual_joint_contDiffOn_slice bbar O hbbar z.1)
      (fun a => actual_joint_contDiffOn_slice (P a) O (hP a) z.1)
      (fun a => actual_joint_contDiffOn_slice (Q a) O (hQ a) z.1)
      (fun a => actual_joint_contDiffOn_slice (Pbar a) O (hPbar a) z.1)
      (fun a => actual_joint_contDiffOn_slice (Qbar a) O (hQbar a) z.1) hz
  refine ⟨heSmooth.congr heq,?_⟩
  intro k hk z hz
  have he : (fun w => err b P Q w-err bbar Pbar Qbar w) =ᶠ[𝓝 z] err bd Pd Qd :=
    eventuallyEq_of_mem (hO.mem_nhds (hSO hz)) (fun w hw => heq hw)
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact (heBound k hk z hz).trans_eq (by unfold actualJointPrimaryErrorCost; ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_primary_error_slow_jets

#print axioms GlobalEmbedding.Continuation.actual_joint_primary_error_difference_slow_jets
