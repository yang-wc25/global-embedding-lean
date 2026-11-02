import Probes.ActualIncrementJointPrimaryError

/-!
# Slow jets of the literal derivative coefficient of complete amplitudes

The amplitudes in this theorem include their normal and reconstructed parts.
The coefficient is the original differentiated primary coefficient. Only its
actual amplitude and primitive phase budgets are inputs. The tau in the
amplitudes cancels the fast phase denominator at every slow derivative order.
-/

noncomputable section
open GlobalEmbedding.Paper Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def round4CompleteCoefficientJetCost (j : ℕ) (v : D) (co : Fin N) (CR CQ Mp : ℝ) : ℝ :=
  (‖ContinuousLinearMap.apply ℝ ℂ v‖ + 2^j*‖actualJointPhaseProduct‖*Mp) *
    (‖incrementsFreeComplexCoordinate co‖*(CR+CQ))

theorem round4_complete_coefficient_slow_jets
    (R Q : X → V) (phi : X → ℝ) (v : D) (co : Fin N)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hR : ContDiffOn ℝ ∞ R O) (hQ : ContDiffOn ℝ ∞ Q O)
    (hphi : ContDiffOn ℝ ∞ phi O)
    (j : ℕ) (tau ell CR CQ Mp : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hCR : 0 ≤ CR) (hCQ : 0 ≤ CQ) (hMp : 0 ≤ Mp)
    (hRb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k R z‖ ≤ CR*tau)
    (hQb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k Q z‖ ≤ CQ*tau)
    (hphib : ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => fderiv ℝ (fun x => phi (w.1,x)) w.2 v) z‖ ≤ Mp) :
    let coeff := fun z : X => incrementsPrimaryDerivativeCoefficient
      (fun x => phi (z.1,x)) tau (fun (_ : Unit) _ => 1)
      (fun _ x => R (z.1,x)) (fun _ x => Q (z.1,x)) z.2 v co
    ContDiffOn ℝ ∞ coeff O ∧ ∀ k ≤ j, ∀ z ∈ S,
      ell^k*‖iteratedFDeriv ℝ k coeff z‖ ≤ round4CompleteCoefficientJetCost j v co CR CQ Mp := by
  intro coeff
  have hell : 0 < ell := htau.trans_le htaul
  let ev := incrementsFreeComplexCoordinate co
  let C := fun z : X => ev (R z)+Complex.I • ev (Q z)
  let C0 := ‖ev‖*(CR+CQ)
  let grad := fun z : X => fderiv ℝ (fun x => phi (z.1,x)) z.2 v
  let dC := fun z : X => fderiv ℝ (fun x => C (z.1,x)) z.2 v
  let fast := fun z : X => tau⁻¹ • actualJointPhaseProduct (grad z) (C z)
  have hC0 : 0 ≤ C0 := mul_nonneg (norm_nonneg _) (add_nonneg hCR hCQ)
  have hRe : ContDiffOn ℝ ∞ (fun z => ev (R z)) O := ev.contDiff.comp_contDiffOn hR
  have hQe : ContDiffOn ℝ ∞ (fun z => ev (Q z)) O := ev.contDiff.comp_contDiffOn hQ
  have hC : ContDiffOn ℝ ∞ C O := hRe.add (hQe.const_smul Complex.I)
  have hCb (k : ℕ) (hk : k ≤ j+1) (z : X) (hz : z ∈ S) :
      ell^k*‖iteratedFDeriv ℝ k C z‖ ≤ C0*tau := by
    have hr := slow_linear_jet_bound ev O hO R hR k ell (CR*tau) hell.le z (hSO hz) (hRb k hk z hz)
    have hq := slow_linear_jet_bound ev O hO Q hQ k ell (CQ*tau) hell.le z (hSO hz) (hQb k hk z hz)
    have hqi : ell^k*‖iteratedFDeriv ℝ k (fun z => Complex.I • ev (Q z)) z‖ ≤ ‖ev‖*(CQ*tau) := by
      rw [iteratedFDeriv_const_smul_apply' (i := k) (a := Complex.I) ((hQe.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp)),
        norm_smul,Complex.norm_I,one_mul]
      exact hq
    exact (actual_joint_slow_add_jet_bound (fun z => ev (R z)) (fun z => Complex.I • ev (Q z))
      k ell _ _ hell.le z ((hRe.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp))
      (((hQe.const_smul Complex.I).contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp)) hr hqi).trans_eq
      (by dsimp only [C0]; ring)
  obtain ⟨hdC,hdCb⟩ := actual_joint_directional_slow_jets C v O S hO hSO hC j ell (C0*tau) hell hCb
  have hgrad : ContDiffOn ℝ ∞ grad O :=
    ((incrementsJointSpatialJets_bridge phi O hO hphi).2.1).clm_apply contDiffOn_const
  have hprod : ContDiffOn ℝ ∞ (fun z : X => actualJointPhaseProduct (grad z) (C z)) O :=
    (actualJointPhaseProduct.contDiff.comp_contDiffOn hgrad).clm_apply hC
  have hfast : ContDiffOn ℝ ∞ fast O := hprod.const_smul tau⁻¹
  have heq : EqOn coeff (fun z => dC z+fast z) O := by
    intro z hz
    have hRs := (actual_joint_contDiffOn_slice R O hR z.1).contDiffAt
      ((hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)
    have hQs := (actual_joint_contDiffOn_slice Q O hQ z.1).contDiffAt
      ((hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)
    have hc := increments_primary_correction_coefficient_eq (fun x => phi (z.1,x)) tau
      (fun (_ : Unit) x => R (z.1,x)) (fun (_ : Unit) x => Q (z.1,x)) z.2 v co
      (fun _ => hRs.differentiableAt (by simp)) (fun _ => hQs.differentiableAt (by simp))
    have hsum : incrementsPrimaryCorrectionSum (fun (_ : Unit) x => R (z.1,x))
        (fun (_ : Unit) x => Q (z.1,x)) co = fun x => C (z.1,x) := by
      funext x
      simp [incrementsPrimaryCorrectionSum,C,ev]
    rw [hsum] at hc
    change coeff z = dC z+Complex.I*(grad z/tau : ℂ)*C z at hc
    rw [hc]
    congr 1
    rw [show fast z = tau⁻¹ • actualJointPhaseProduct (grad z) (C z) from rfl,
      actualJointPhaseProduct_apply,Complex.real_smul]
    push_cast
    ring
  refine ⟨(hdC.add hfast).congr heq,?_⟩
  intro k hk z hz
  have hdCb' : ell^k*‖iteratedFDeriv ℝ k dC z‖ ≤ ‖ContinuousLinearMap.apply ℝ ℂ v‖*C0 := by
    apply (hdCb k hk z hz).trans
    rw [mul_div_assoc,mul_div_assoc]
    calc
      _ ≤ ‖ContinuousLinearMap.apply ℝ ℂ v‖*(C0*1) := by
        gcongr
        exact (div_le_one hell).mpr htaul
      _ = _ := by ring
  have hp := slow_bilinear_jet_bound_norm actualJointPhaseProduct O hO grad C hgrad hC k ell Mp
    (C0*tau) hell.le z (hSO hz) (fun a ha => hphib a (ha.trans hk) z hz)
    (fun a ha => hCb a (by omega) z hz)
  have hfastb : ell^k*‖iteratedFDeriv ℝ k fast z‖ ≤ 2^j*‖actualJointPhaseProduct‖*Mp*C0 := by
    change ell^k*‖iteratedFDeriv ℝ k (fun y => tau⁻¹ • actualJointPhaseProduct (grad y) (C y)) z‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hprod.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp)),
      norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos htau]
    calc
      _ = tau⁻¹*(ell^k*‖iteratedFDeriv ℝ k (fun y => actualJointPhaseProduct (grad y) (C y)) z‖) := by ring
      _ ≤ tau⁻¹*(2^k*(‖actualJointPhaseProduct‖*Mp)*(C0*tau)) :=
        mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr htau.le)
      _ = 2^k*‖actualJointPhaseProduct‖*Mp*C0 := by field_simp [htau.ne']
      _ ≤ _ := by gcongr; norm_num
  have hb := actual_joint_slow_add_jet_bound dC fast k ell _ _ hell.le z
    ((hdC.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp))
    ((hfast.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp)) hdCb' hfastb
  have hg : coeff =ᶠ[𝓝 z] (fun z => dC z+fast z) :=
    eventuallyEq_of_mem (hO.mem_nhds (hSO hz)) (fun y hy => heq hy)
  rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hb.trans_eq (by dsimp only [round4CompleteCoefficientJetCost,C0,ev]; ring)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_complete_coefficient_slow_jets
