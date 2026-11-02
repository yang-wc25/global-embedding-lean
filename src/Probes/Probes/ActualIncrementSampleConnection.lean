import Probes.ActualIncrementSampleGram
import Probes.ActualAdaptedConnectionJets

/-! The SAME actual induced connection has shift one on the original samples,
while remaining smooth on its actual open injectivity domain. No budget is
assumed outside the original sampling set and the original constants stay fixed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {X E V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

local instance sampledConnectionEVNormedGroup : NormedAddCommGroup (E →L[ℝ] V) := inferInstance
local instance sampledConnectionEVNormedSpace : NormedSpace ℝ (E →L[ℝ] V) := inferInstance
local instance sampledConnectionEENormedGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance sampledConnectionEENormedSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance sampledConnectionVENormedGroup : NormedAddCommGroup (V →L[ℝ] E) := inferInstance
local instance sampledConnectionVENormedSpace : NormedSpace ℝ (V →L[ℝ] E) := inferInstance
local instance sampledConnectionIntermediateNormedGroup : NormedAddCommGroup ((E →L[ℝ] V) →L[ℝ] (E →L[ℝ] E)) := inferInstance
local instance sampledConnectionIntermediateNormedSpace : NormedSpace ℝ ((E →L[ℝ] V) →L[ℝ] (E →L[ℝ] E)) := inferInstance
-- Cache the ordinary operator-space instances at the two Hessian spaces.
-- This avoids repeated expansion of deeply curried norm instances.
local instance sampledConnectionHessianNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance sampledConnectionHessianNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance sampledConnectionTargetNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sampledConnectionTargetNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem actualConnectionFromJets_slow_jets_on_samples
    (A : X → E →L[ℝ] V) (H : X → E →L[ℝ] E →L[ℝ] V)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O) (hA : ContDiffOn ℝ ∞ A O) (hH : ContDiffOn ℝ ∞ H O)
    (hinj : ∀ x ∈ O, Function.Injective (A x))
    (j : ℕ) (ell c MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ x ∈ S, ∀ v : E, c * ‖v‖^2 ≤ ‖A x v‖^2)
    (hAj : ∀ k ≤ j, ∀ x ∈ S, ell^k * ‖iteratedFDeriv ℝ k A x‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ x ∈ S, ell^k * ‖iteratedFDeriv ℝ k H x‖ ≤ MH) :
    ContDiffOn ℝ ∞ (actualConnectionFromJets A H) O ∧
    ∀ k ≤ j, ∀ x ∈ S, ell^k * ‖iteratedFDeriv ℝ k (actualConnectionFromJets A H) x‖ ≤
      actualConnectionSlowConstant j c MA MH := by
  let R := slowInverseMajorant c⁻¹ (2^j * MA^2) j
  have hR : 0 ≤ R := slowInverseMajorant_nonneg (inv_nonneg.mpr hc.le) (by positivity) j
  let G : X → E →L[ℝ] E := fun x => ((A x).adjoint.comp (A x)).inverse
  obtain ⟨hG,hGb⟩ := actual_gram_inverse_slow_jets_on_samples A O S hO hSO hA hinj j ell c MA hell hc hMA hreserve hAj
  let adj : (E →L[ℝ] V) →L[ℝ] (V →L[ℝ] E) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := V)).toContinuousLinearEquiv.toContinuousLinearMap
  have hadj : ContDiffOn ℝ ∞ (fun x => (A x).adjoint) O := adj.contDiff.comp_contDiffOn hA
  have hadjb := actual_adjoint_slow_jets A j ell MA S hAj
  let Q : X → V →L[ℝ] E := fun x => (G x).comp (A x).adjoint
  have hQ : ContDiffOn ℝ ∞ Q O := hG.clm_comp hadj
  have hQb : ∀ k ≤ j, ∀ x ∈ S, ell^k * ‖iteratedFDeriv ℝ k Q x‖ ≤ 2^j * R * MA := by
    intro k hk x hx
    have hb := slow_bilinear_jet_bound (ContinuousLinearMap.compL ℝ V E E)
      (ContinuousLinearMap.norm_compL_le ℝ V E E) O hO G (fun x => (A x).adjoint)
      hG hadj k ell R MA hell.le hR x (hSO hx)
      (fun a ha => hGb a (ha.trans hk) x hx) (fun a ha => hadjb a (ha.trans hk) x hx)
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hR) hMA)
  let L := actualConnectionPairing E V
  have hC : ContDiffOn ℝ ∞ (actualConnectionFromJets A H) O := by
    change ContDiffOn ℝ ∞ (fun x =>
      (ContinuousLinearMap.compL ℝ E V E (Q x)).comp (H x)) O
    exact ((ContinuousLinearMap.compL ℝ E V E).contDiff.comp_contDiffOn hQ).clm_comp hH
  refine ⟨hC, ?_⟩
  intro k hk x hx
  have hL : ‖L‖ ≤ 1 := actualConnectionPairing_norm_le (E := E) (V := V)
  have hb := slow_bilinear_jet_bound L hL O hO Q H hQ hH k ell (2^j * R * MA) MH hell.le
    (by positivity) x (hSO hx)
    (fun a ha => hQb a (ha.trans hk) x hx) (fun a ha => hHj a (ha.trans hk) x hx)
  apply hb.trans
  unfold actualConnectionSlowConstant
  change 2^k * (2^j * R * MA) * MH ≤ 2^j * (2^j * R * MA) * MH
  calc
    _ ≤ 2^j * (2^j * R * MA) * MH :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hk) (by positivity)) hMH
    _ = _ := by ring

theorem actualConnectionFromJets_shift_one_jets_on_samples
    (A : X → E →L[ℝ] V) (H : X → E →L[ℝ] E →L[ℝ] V)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O) (hA : ContDiffOn ℝ ∞ A O) (hH : ContDiffOn ℝ ∞ H O)
    (hinj : ∀ x ∈ O, Function.Injective (A x))
    (j : ℕ) (ell c MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ x ∈ S, ∀ v : E, c*‖v‖^2 ≤ ‖A x v‖^2)
    (hAj : ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k A x‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ x ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k H x‖ ≤ MH) :
    ContDiffOn ℝ ∞ (actualConnectionFromJets A H) O ∧
      ∀ k ≤ j, ∀ x ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k (actualConnectionFromJets A H) x‖ ≤
        actualConnectionSlowConstant j c MA MH := by
  have hH0 : ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k H x‖ ≤ MH/ell := by
    intro k hk x hx
    apply (le_div_iff₀ hell).2
    simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using hHj k hk x hx
  obtain ⟨hs,hb⟩ := actualConnectionFromJets_slow_jets_on_samples A H O S hO hSO hA hH hinj j ell c MA (MH/ell)
    hell hc hMA (div_nonneg hMH hell.le) hreserve hAj hH0
  refine ⟨hs,?_⟩
  intro k hk x hx
  calc
    _ = (ell^k*‖iteratedFDeriv ℝ k (actualConnectionFromJets A H) x‖)*ell := by rw [pow_succ]; ring
    _ ≤ actualConnectionSlowConstant j c MA (MH/ell)*ell :=
      mul_le_mul_of_nonneg_right (hb k hk x hx) hell.le
    _ = actualConnectionSlowConstant j c MA MH := by
      unfold actualConnectionSlowConstant
      field_simp
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualConnectionFromJets_slow_jets_on_samples
#print axioms GlobalEmbedding.Continuation.actualConnectionFromJets_shift_one_jets_on_samples
