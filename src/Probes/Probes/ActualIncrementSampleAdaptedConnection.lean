import Probes.ActualIncrementSampleConnection
import Probes.ActualIncrementSampleFirstFrame

/-! The original T0 and Gamma fields with their genuine shift one are
produced on the actual samples, without budgets outside those samples. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

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

theorem actual_adapted_T0_gamma_on_samples
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ)
    (F : Ep → M → V) (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (U W S S0 : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hSU : S ⊆ U) (hS0W : S0 ⊆ W)
    (hF0 : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hmap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (hsample : MapsTo (actualSourceChartTransition e0 e1) S S0)
    (hinj : ∀ z ∈ U, Function.Injective (fderiv ℝ (F z.1 ∘ (e1 z.1).symm) z.2))
    (hcoord : ∀ z ∈ U, (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (ell K c : ℝ) (hell : 0 < ell) (hK : 0 ≤ K) (hc : 0 < c)
    (hreserve : ∀ z ∈ S, ∀ v : D,
      c*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e1 z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ j+1, ∀ z ∈ S0, ell^k*‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e0 y.1).symm) y.2) z‖ ≤ K)
    (hphijet : ∀ k, 1 ≤ k → k ≤ j+2 → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k (actualSourceChartTransition e0 e1) z‖ ≤ T k) :
    let C := actualFirstFrameTransferCost T (j+1)*K
    (ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (e1 z.1).symm z.2) U ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k
        (fun y : X => incrementsModeTransverseValue (F y.1) (e1 y.1).symm y.2) z‖ ≤
          actualIncrementT0Constant m j c C C) ∧
    (ContDiffOn ℝ ∞ (fun z : X => actualIncrementFullRowPairing m (m+1)
      (fun i => incrementsModeGamma (F z.1) (e1 z.1).symm z.2 0 i)) U ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k
        (fun y : X => actualIncrementFullRowPairing m (m+1)
          (fun i => incrementsModeGamma (F y.1) (e1 y.1).symm y.2 0 i)) z‖ ≤
          actualIncrementGammaRowConstant m j c C C) := by
  dsimp only
  let C := actualFirstFrameTransferCost T (j+1)*K
  have hC : 0 ≤ C := mul_nonneg (actualFirstFrameTransferCost_nonneg T hT _) hK
  obtain ⟨_,hA,hH,hb⟩ := actual_first_frame_hessian_transferred_on_samples T hT j F e0 e1
    U W S S0 hU hW hSU hS0W hF0 hphi hmap hsample hcoord ell K hell hK hAj hphijet
  let A : X → D →L[ℝ] V := fun z => fderiv ℝ (F z.1 ∘ (e1 z.1).symm) z.2
  let H : X → D →L[ℝ] D →L[ℝ] V := fun z => fderiv ℝ (fderiv ℝ (F z.1 ∘ (e1 z.1).symm)) z.2
  let G := actualConnectionFromJets A H
  obtain ⟨hG,hGb⟩ := actualConnectionFromJets_shift_one_jets_on_samples A H U S hU hSU hA hH hinj j ell c C C
    hell hc hC hC hreserve (fun k hk z hz => (hb k hk z hz).1) (fun k hk z hz => (hb k hk z hz).2)
  have ht : (fun z : X => incrementsModeTransverseValue (F z.1) (e1 z.1).symm z.2) =
      actualIncrementTransverseValueFromGamma m ∘ G :=
    funext fun z => actual_increment_transverse_value_from_connection (F z.1) (e1 z.1).symm z.2
  rw [ht]
  constructor
  · refine ⟨(actualIncrementTransverseValueFromGamma m).contDiff.comp_contDiffOn hG,?_⟩
    intro k hk z hz
    exact actual_slow_shift_one_linear_jet (actualIncrementTransverseValueFromGamma m) G U hU hG
      k ell (actualConnectionSlowConstant j c C C) hell z (hSU hz) (hGb k hk z hz)
  · change ContDiffOn ℝ ∞ (actualIncrementGammaRowOperator m ∘ G) U ∧ _
    refine ⟨(actualIncrementGammaRowOperator m).contDiff.comp_contDiffOn hG,?_⟩
    intro k hk z hz
    exact actual_slow_shift_one_linear_jet (actualIncrementGammaRowOperator m) G U hU hG
      k ell (actualConnectionSlowConstant j c C C) hell z (hSU hz) (hGb k hk z hz)
end Original
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_adapted_T0_gamma_on_samples
