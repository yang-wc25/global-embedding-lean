import Probes.ActualFixedMetricSecondForm
import Smoothing.WeightedActualOperations

/-!
# Actual induced connection slow jets from primitive geometric jets

The connection is built from the same actual first derivative, Gram inverse
and Hessian. A fixed frame reserve produces its inverse bounds; the remaining
bounds follow by native Leibniz estimates. The final theorem identifies the
result with probeInducedConnection, rather than a replacement connection.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff
namespace GlobalEmbedding.Continuation

section Algebra
variable (E V : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def actualConnectionPairing : (V →L[ℝ] E) →L[ℝ] (E →L[ℝ] E →L[ℝ] V) →L[ℝ] (E →L[ℝ] E →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] V) (E →L[ℝ] E)).comp
    (ContinuousLinearMap.compL ℝ E V E)

def actualConnectionSlowConstant (j : ℕ) (c MA MH : ℝ) : ℝ :=
  2^j * (2^j * slowInverseMajorant c⁻¹ (2^j * MA^2) j * MA) * MH

theorem actualConnectionSlowConstant_nonneg (j : ℕ) {c MA MH : ℝ}
    (hc : 0 < c) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH) :
    0 ≤ actualConnectionSlowConstant j c MA MH := by
  have hR := slowInverseMajorant_nonneg (inv_nonneg.mpr hc.le)
    (by positivity : 0 ≤ 2^j * MA^2) j
  unfold actualConnectionSlowConstant
  positivity
end Algebra

section Bounds
variable {X E V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

local instance connectionEVNormedGroup : NormedAddCommGroup (E →L[ℝ] V) := inferInstance
local instance connectionEVNormedSpace : NormedSpace ℝ (E →L[ℝ] V) := inferInstance
local instance connectionEENormedGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance connectionEENormedSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance connectionVENormedGroup : NormedAddCommGroup (V →L[ℝ] E) := inferInstance
local instance connectionVENormedSpace : NormedSpace ℝ (V →L[ℝ] E) := inferInstance
local instance connectionIntermediateNormedGroup : NormedAddCommGroup ((E →L[ℝ] V) →L[ℝ] (E →L[ℝ] E)) := inferInstance
local instance connectionIntermediateNormedSpace : NormedSpace ℝ ((E →L[ℝ] V) →L[ℝ] (E →L[ℝ] E)) := inferInstance
-- Cache the ordinary operator-space instances at the two Hessian spaces.
-- This avoids repeated expansion of deeply curried norm instances.
local instance connectionHessianNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance connectionHessianNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance connectionTargetNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance connectionTargetNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

def actualConnectionFromJets (A : X → E →L[ℝ] V) (H : X → E →L[ℝ] E →L[ℝ] V)
    (x : X) : E →L[ℝ] E →L[ℝ] E :=
  actualConnectionPairing E V (((A x).adjoint.comp (A x)).inverse.comp (A x).adjoint) (H x)

/-- The concrete Hessian-composition pairing has operator norm at most one. -/
theorem actualConnectionPairing_norm_le : ‖actualConnectionPairing E V‖ ≤ 1 := by
  let L₀ := ContinuousLinearMap.compL ℝ E (E →L[ℝ] V) (E →L[ℝ] E)
  let L₁ := ContinuousLinearMap.compL ℝ E V E
  change ‖L₀.comp L₁‖ ≤ 1
  have h₀ : ‖L₀‖ ≤ 1 := ContinuousLinearMap.norm_compL_le ℝ E (E →L[ℝ] V) (E →L[ℝ] E)
  have h₁ : ‖L₁‖ ≤ 1 := ContinuousLinearMap.norm_compL_le ℝ E V E
  exact (ContinuousLinearMap.opNorm_comp_le L₀ L₁).trans
    (by simpa using mul_le_mul h₀ h₁ L₁.opNorm_nonneg zero_le_one)

/-- Every joint derivative of the actual connection is bounded from actual
first/Hessian slow jets and the fixed injectivity reserve. -/
theorem actualConnectionFromJets_slow_jets
    (A : X → E →L[ℝ] V) (H : X → E →L[ℝ] E →L[ℝ] V)
    (O : Set X) (hO : IsOpen O) (hA : ContDiffOn ℝ ∞ A O) (hH : ContDiffOn ℝ ∞ H O)
    (j : ℕ) (ell c MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ x ∈ O, ∀ v : E, c * ‖v‖^2 ≤ ‖A x v‖^2)
    (hAj : ∀ k ≤ j, ∀ x ∈ O, ell^k * ‖iteratedFDeriv ℝ k A x‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ x ∈ O, ell^k * ‖iteratedFDeriv ℝ k H x‖ ≤ MH) :
    ContDiffOn ℝ ∞ (actualConnectionFromJets A H) O ∧
    ∀ k ≤ j, ∀ x ∈ O, ell^k * ‖iteratedFDeriv ℝ k (actualConnectionFromJets A H) x‖ ≤
      actualConnectionSlowConstant j c MA MH := by
  let R := slowInverseMajorant c⁻¹ (2^j * MA^2) j
  have hR : 0 ≤ R := slowInverseMajorant_nonneg (inv_nonneg.mpr hc.le) (by positivity) j
  let G : X → E →L[ℝ] E := fun x => ((A x).adjoint.comp (A x)).inverse
  obtain ⟨hG,hGb⟩ := actual_gram_inverse_slow_jets A O hO hA j ell c MA hell hc hMA hreserve hAj
  let adj : (E →L[ℝ] V) →L[ℝ] (V →L[ℝ] E) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := V)).toContinuousLinearEquiv.toContinuousLinearMap
  have hadj : ContDiffOn ℝ ∞ (fun x => (A x).adjoint) O := adj.contDiff.comp_contDiffOn hA
  have hadjb := actual_adjoint_slow_jets A j ell MA O hAj
  let Q : X → V →L[ℝ] E := fun x => (G x).comp (A x).adjoint
  have hQ : ContDiffOn ℝ ∞ Q O := hG.clm_comp hadj
  have hQb : ∀ k ≤ j, ∀ x ∈ O, ell^k * ‖iteratedFDeriv ℝ k Q x‖ ≤ 2^j * R * MA := by
    intro k hk x hx
    have hb := slow_bilinear_jet_bound (ContinuousLinearMap.compL ℝ V E E)
      (ContinuousLinearMap.norm_compL_le ℝ V E E) O hO G (fun x => (A x).adjoint)
      hG hadj k ell R MA hell.le hR x hx
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
    (by positivity) x hx
    (fun a ha => hQb a (ha.trans hk) x hx) (fun a ha => hHj a (ha.trans hk) x hx)
  apply hb.trans
  unfold actualConnectionSlowConstant
  change 2^k * (2^j * R * MA) * MH ≤ 2^j * (2^j * R * MA) * MH
  calc
    _ ≤ 2^j * (2^j * R * MA) * MH :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hk) (by positivity)) hMH
    _ = _ := by ring
end Bounds

/-- Exact specialization to the already proved native induced connection.
Both spatial derivatives are actual derivatives of the same family F. -/
theorem actualConnectionFromJets_eq_probeInducedConnection
    {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {n N : ℕ}
    (F : Ep → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (z : Ep × EuclideanSpace ℝ (Fin n)) :
    actualConnectionFromJets (fun y => fderiv ℝ (F y.1) y.2)
      (fun y => fderiv ℝ (fderiv ℝ (F y.1)) y.2) z = probeInducedConnection (F z.1) z.2 := rfl

/-- All joint slow jets of the actual induced connection of the SAME family,
expressed directly through its genuine spatial first and second derivatives. -/
theorem probeInducedConnection_slow_jets
    {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {n N : ℕ}
    (F : Ep → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (O : Set (Ep × EuclideanSpace ℝ (Fin n))) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (fun z : Ep × EuclideanSpace ℝ (Fin n) => fderiv ℝ (F z.1) z.2) O)
    (hH : ContDiffOn ℝ ∞ (fun z : Ep × EuclideanSpace ℝ (Fin n) =>
      fderiv ℝ (fderiv ℝ (F z.1)) z.2) O)
    (j : ℕ) (ell c MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ O, ∀ v : EuclideanSpace ℝ (Fin n), c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1) z.2 v‖^2)
    (hAj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : Ep × EuclideanSpace ℝ (Fin n) => fderiv ℝ (F y.1) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : Ep × EuclideanSpace ℝ (Fin n) => fderiv ℝ (fderiv ℝ (F y.1)) y.2) z‖ ≤ MH) :
    ContDiffOn ℝ ∞ (fun z => probeInducedConnection (F z.1) z.2) O ∧
    ∀ k ≤ j, ∀ z ∈ O, ell^k *
      ‖iteratedFDeriv ℝ k (fun y => probeInducedConnection (F y.1) y.2) z‖ ≤
        actualConnectionSlowConstant j c MA MH := by
  have he : (fun z : Ep × EuclideanSpace ℝ (Fin n) => probeInducedConnection (F z.1) z.2) =
      actualConnectionFromJets (fun z => fderiv ℝ (F z.1) z.2)
        (fun z => fderiv ℝ (fderiv ℝ (F z.1)) z.2) :=
    funext (fun z => (actualConnectionFromJets_eq_probeInducedConnection F z).symm)
  rw [he]
  exact actualConnectionFromJets_slow_jets _ _ O hO hA hH j ell c MA MH hell hc hMA hMH
    hreserve hAj hHj

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualConnectionFromJets_slow_jets
#print axioms GlobalEmbedding.Continuation.actualConnectionFromJets_eq_probeInducedConnection

#print axioms GlobalEmbedding.Continuation.probeInducedConnection_slow_jets
