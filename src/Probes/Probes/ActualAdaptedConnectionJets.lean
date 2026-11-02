import Probes.ActualFirstFrameChartTransfer
import Probes.ActualIncrementGeometricJets

/-!
# Actual adapted connection and transverse value with the correct slow shift

The actual connection is linear in the ordinary Hessian. The latter has
shift one in an adapted phase chart, while the first frame has shift zero.
The resulting connection, original Gamma rows and original T0 consequently
have exactly shift one. All constants remain independent of ell.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

section Shift
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem actual_slow_shift_one_linear_jet
    (L : Y →L[ℝ] Z) (f : X → Y) (O : Set X) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (k : ℕ) (ell K : ℝ) (hell : 0 < ell)
    (x : X) (hx : x ∈ O)
    (hb : ell^(k+1)*‖iteratedFDeriv ℝ k f x‖ ≤ K) :
    ell^(k+1)*‖iteratedFDeriv ℝ k (L ∘ f) x‖ ≤ ‖L‖*K := by
  have h0 : ell^k*‖iteratedFDeriv ℝ k f x‖ ≤ K/ell := by
    apply (le_div_iff₀ hell).2
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hb
  have h := slow_linear_jet_bound L O hO f hf k ell (K/ell) hell.le x hx h0
  calc
    _ = (ell^k*‖iteratedFDeriv ℝ k (L ∘ f) x‖)*ell := by rw [pow_succ]; ring
    _ ≤ (‖L‖*(K/ell))*ell := mul_le_mul_of_nonneg_right h hell.le
    _ = ‖L‖*K := by field_simp
end Shift

section Connection
variable {X E V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

private local instance adaptedFirstNormed : NormedAddCommGroup (E →L[ℝ] V) := inferInstance
private local instance adaptedFirstSpace : NormedSpace ℝ (E →L[ℝ] V) := inferInstance
private local instance adaptedHessianNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := inferInstance
private local instance adaptedHessianSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := inferInstance
private local instance adaptedConnectionNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
private local instance adaptedConnectionSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem actualConnectionFromJets_shift_one_jets
    (A : X → E →L[ℝ] V) (H : X → E →L[ℝ] E →L[ℝ] V)
    (O : Set X) (hO : IsOpen O) (hA : ContDiffOn ℝ ∞ A O) (hH : ContDiffOn ℝ ∞ H O)
    (j : ℕ) (ell c MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ x ∈ O, ∀ v : E, c*‖v‖^2 ≤ ‖A x v‖^2)
    (hAj : ∀ k ≤ j, ∀ x ∈ O, ell^k*‖iteratedFDeriv ℝ k A x‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ x ∈ O, ell^(k+1)*‖iteratedFDeriv ℝ k H x‖ ≤ MH) :
    ContDiffOn ℝ ∞ (actualConnectionFromJets A H) O ∧
      ∀ k ≤ j, ∀ x ∈ O, ell^(k+1)*‖iteratedFDeriv ℝ k (actualConnectionFromJets A H) x‖ ≤
        actualConnectionSlowConstant j c MA MH := by
  have hH0 : ∀ k ≤ j, ∀ x ∈ O, ell^k*‖iteratedFDeriv ℝ k H x‖ ≤ MH/ell := by
    intro k hk x hx
    apply (le_div_iff₀ hell).2
    simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using hHj k hk x hx
  obtain ⟨hs,hb⟩ := actualConnectionFromJets_slow_jets A H O hO hA hH j ell c MA (MH/ell)
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
end Connection

section Original
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]

private local instance adaptedDDNormed : NormedAddCommGroup (D →L[ℝ] D) := inferInstance
private local instance adaptedDDSpace : NormedSpace ℝ (D →L[ℝ] D) := inferInstance
private local instance adaptedGGNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] D) := inferInstance
private local instance adaptedGGSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] D) := inferInstance
private local instance adaptedTNormed : NormedAddCommGroup (D →L[ℝ] Tdata) := inferInstance
private local instance adaptedTSpace : NormedSpace ℝ (D →L[ℝ] Tdata) := inferInstance

/-- The original T0 and Gamma rows are produced from original first jets and
the real adapted chart, not from output connection or coefficient budgets. -/
theorem actual_adapted_T0_gamma_from_original_jets
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ)
    (F : Ep → M → V) (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (U W : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hF0 : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hmap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (hcoord : ∀ z ∈ U, (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (ell K c : ℝ) (hell : 0 < ell) (hK : 0 ≤ K) (hc : 0 < c)
    (hreserve : ∀ z ∈ U, ∀ v : D,
      c*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e1 z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ j+1, ∀ z ∈ W, ell^k*‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e0 y.1).symm) y.2) z‖ ≤ K)
    (hphijet : ∀ k, 1 ≤ k → k ≤ j+2 → ∀ z ∈ U,
      ell^(k-1)*‖iteratedFDeriv ℝ k (actualSourceChartTransition e0 e1) z‖ ≤ T k) :
    let C := actualFirstFrameTransferCost T (j+1)*K
    (ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (e1 z.1).symm z.2) U ∧
      ∀ k ≤ j, ∀ z ∈ U, ell^(k+1)*‖iteratedFDeriv ℝ k
        (fun y : X => incrementsModeTransverseValue (F y.1) (e1 y.1).symm y.2) z‖ ≤
          actualIncrementT0Constant m j c C C) ∧
    (ContDiffOn ℝ ∞ (fun z : X => actualIncrementFullRowPairing m (m+1)
      (fun i => incrementsModeGamma (F z.1) (e1 z.1).symm z.2 0 i)) U ∧
      ∀ k ≤ j, ∀ z ∈ U, ell^(k+1)*‖iteratedFDeriv ℝ k
        (fun y : X => actualIncrementFullRowPairing m (m+1)
          (fun i => incrementsModeGamma (F y.1) (e1 y.1).symm y.2 0 i)) z‖ ≤
          actualIncrementGammaRowConstant m j c C C) := by
  dsimp only
  let C := actualFirstFrameTransferCost T (j+1)*K
  have hC : 0 ≤ C := mul_nonneg (actualFirstFrameTransferCost_nonneg T hT _) hK
  obtain ⟨_,hA,hH,hb⟩ := actual_first_frame_hessian_transferred_from_original_jets T hT j F e0 e1
    U W hU hW hF0 hphi hmap hcoord ell K hell hK hAj hphijet
  let A : X → D →L[ℝ] V := fun z => fderiv ℝ (F z.1 ∘ (e1 z.1).symm) z.2
  let H : X → D →L[ℝ] D →L[ℝ] V := fun z => fderiv ℝ (fderiv ℝ (F z.1 ∘ (e1 z.1).symm)) z.2
  let G := actualConnectionFromJets A H
  obtain ⟨hG,hGb⟩ := actualConnectionFromJets_shift_one_jets A H U hU hA hH j ell c C C
    hell hc hC hC hreserve (fun k hk z hz => (hb k hk z hz).1) (fun k hk z hz => (hb k hk z hz).2)
  have ht : (fun z : X => incrementsModeTransverseValue (F z.1) (e1 z.1).symm z.2) =
      actualIncrementTransverseValueFromGamma m ∘ G :=
    funext fun z => actual_increment_transverse_value_from_connection (F z.1) (e1 z.1).symm z.2
  rw [ht]
  constructor
  · refine ⟨(actualIncrementTransverseValueFromGamma m).contDiff.comp_contDiffOn hG,?_⟩
    intro k hk z hz
    exact actual_slow_shift_one_linear_jet (actualIncrementTransverseValueFromGamma m) G U hU hG
      k ell (actualConnectionSlowConstant j c C C) hell z hz (hGb k hk z hz)
  · change ContDiffOn ℝ ∞ (actualIncrementGammaRowOperator m ∘ G) U ∧ _
    refine ⟨(actualIncrementGammaRowOperator m).contDiff.comp_contDiffOn hG,?_⟩
    intro k hk z hz
    exact actual_slow_shift_one_linear_jet (actualIncrementGammaRowOperator m) G U hU hG
      k ell (actualConnectionSlowConstant j c C C) hell z hz (hGb k hk z hz)
end Original

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualConnectionFromJets_shift_one_jets
#print axioms GlobalEmbedding.Continuation.actual_adapted_T0_gamma_from_original_jets
