import Probes.ActualIncrementCoefficientMaps

/-!
# Original J and T0 budgets from primitive geometry

The original included transverse J now receives its actual frame jets from
the same projected Hessian, while the transverse reserve remains an explicit
chosen-phase input. The original T0 and Gamma-row fields are fixed linear
observations of the actual induced connection, whose inverse bound is derived
from the first-frame reserve. All constants are independent of small scales.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

private local instance geometricDDNormed (m : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance geometricDDSpace (m : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance geometricHessianNormed (m : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance geometricHessianSpace (m : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance geometricT0Normed (m : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2}) := inferInstance
private local instance geometricT0Space (m : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2}) := inferInstance


def actualIncrementJConstant (m N j : ℕ) (c cT MA MH : ℝ) : ℝ :=
  let MC := actualIncrementTransverseFrameConstant m N j c MA MH
  2^j * MC * slowInverseMajorant cT⁻¹ (2^j * MC^2) j

def actualIncrementT0Constant (m j : ℕ) (c MA MH : ℝ) : ℝ :=
  ‖actualIncrementTransverseValueFromGamma m‖ * actualConnectionSlowConstant j c MA MH

def actualIncrementGammaRowConstant (m j : ℕ) (c MA MH : ℝ) : ℝ :=
  ‖actualIncrementGammaRowOperator m‖ * actualConnectionSlowConstant j c MA MH

theorem actualIncrementJConstant_nonneg (m N j : ℕ) {c cT MA MH : ℝ}
    (hc : 0 < c) (hcT : 0 < cT) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH) :
    0 ≤ actualIncrementJConstant m N j c cT MA MH := by
  have hMC := actualIncrementTransverseFrameConstant_nonneg m N j hc hMA hMH
  have hR := slowInverseMajorant_nonneg (inv_nonneg.mpr hcT.le)
    (by positivity : 0 ≤ 2^j * (actualIncrementTransverseFrameConstant m N j c MA MH)^2) j
  unfold actualIncrementJConstant
  positivity

theorem actualIncrementT0Constant_nonneg (m j : ℕ) {c MA MH : ℝ}
    (hc : 0 < c) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH) :
    0 ≤ actualIncrementT0Constant m j c MA MH :=
  mul_nonneg (actualIncrementTransverseValueFromGamma m).opNorm_nonneg
    (actualConnectionSlowConstant_nonneg j hc hMA hMH)

theorem actualIncrementGammaRowConstant_nonneg (m j : ℕ) {c MA MH : ℝ}
    (hc : 0 < c) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH) :
    0 ≤ actualIncrementGammaRowConstant m j c MA MH :=
  mul_nonneg (actualIncrementGammaRowOperator m).opNorm_nonneg
    (actualConnectionSlowConstant_nonneg j hc hMA hMH)

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

section PrimitiveInputs

/-- The original J bound uses primitive first/Hessian jets and the actual
chosen transverse reserve; no transverse frame or J output budget is assumed. -/
theorem actual_increment_transverse_J_from_primitive_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hA : ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2) O)
    (hH : ContDiffOn ℝ ∞ (fun z : X =>
      fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2) O)
    (j : ℕ) (ell c MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ O, ∀ v : D,
      c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH)
    (cT : ℝ) (hcT : 0 < cT)
    (hTreserve : ∀ z ∈ O, ∀ v : Tdata,
      cT * ‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame (I := 𝓙)
        (F z.1) (hF z.1) (e z.1).symm z.2 v‖^2) :
    let J := fun z : X =>
      (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2)
    ContDiffOn ℝ ∞ J O ∧
    ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k J z‖ ≤
      actualIncrementJConstant m N j c cT MA MH := by
  obtain ⟨hC,hCb⟩ := actual_increment_transverse_frame_slow_jets F hF e he O hO hcoord
    hA hH j ell c MA MH hell hc hMA hMH hreserve hAj hHj
  exact actual_original_transverse_J_slow_jets F hF (fun p => (e p).symm) O hO hC j ell cT
    (actualIncrementTransverseFrameConstant m N j c MA MH) hell hcT
    (actualIncrementTransverseFrameConstant_nonneg m N j hc hMA hMH) hTreserve hCb

/-- The same actual transverse value coefficient is bounded from actual
first/Hessian jets and the induced-connection producer. -/
theorem actual_increment_transverse_value_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hA : ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2) O)
    (hH : ContDiffOn ℝ ∞ (fun z : X =>
      fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2) O)
    (j : ℕ) (ell c MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ O, ∀ v : D,
      c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH) :
    ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (e z.1).symm z.2) O ∧
    ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => incrementsModeTransverseValue (F y.1) (e y.1).symm y.2) z‖ ≤
        actualIncrementT0Constant m j c MA MH := by
  let A : X → D →L[ℝ] V := fun z => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2
  let H : X → D →L[ℝ] D →L[ℝ] V := fun z => fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2
  let G := actualConnectionFromJets A H
  let L := actualIncrementTransverseValueFromGamma m
  obtain ⟨hG,hGb⟩ := actualConnectionFromJets_slow_jets A H O hO hA hH j ell c MA MH
    hell hc hMA hMH hreserve hAj hHj
  have hEq : (fun z : X => incrementsModeTransverseValue (F z.1) (e z.1).symm z.2) = L ∘ G :=
    funext fun z => actual_increment_transverse_value_from_connection (F z.1) (e z.1).symm z.2
  rw [hEq]
  refine ⟨L.contDiff.comp_contDiffOn hG, ?_⟩
  intro k hk z hz
  exact slow_linear_jet_bound L O hO G hG k ell
    (actualConnectionSlowConstant j c MA MH) hell.le z hz (hGb k hk z hz)

/-- The original Gamma rows with their original weights are bounded as
actual fixed observations of the same induced connection. -/
theorem actual_increment_gamma_row_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hA : ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2) O)
    (hH : ContDiffOn ℝ ∞ (fun z : X =>
      fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2) O)
    (j : ℕ) (ell c MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ O, ∀ v : D,
      c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH) :
    let Grows := fun z : X => actualIncrementFullRowPairing m (m+1)
      (fun i => incrementsModeGamma (F z.1) (e z.1).symm z.2 0 i)
    ContDiffOn ℝ ∞ Grows O ∧
    ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k Grows z‖ ≤
      actualIncrementGammaRowConstant m j c MA MH := by
  let A : X → D →L[ℝ] V := fun z => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2
  let H : X → D →L[ℝ] D →L[ℝ] V := fun z => fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2
  let G := actualConnectionFromJets A H
  let L := actualIncrementGammaRowOperator m
  obtain ⟨hG,hGb⟩ := actualConnectionFromJets_slow_jets A H O hO hA hH j ell c MA MH
    hell hc hMA hMH hreserve hAj hHj
  change ContDiffOn ℝ ∞ (L ∘ G) O ∧ _
  refine ⟨L.contDiff.comp_contDiffOn hG, ?_⟩
  intro k hk z hz
  exact slow_linear_jet_bound L O hO G hG k ell
    (actualConnectionSlowConstant j c MA MH) hell.le z hz (hGb k hk z hz)

end PrimitiveInputs
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_transverse_J_from_primitive_jets
#print axioms GlobalEmbedding.Continuation.actual_increment_transverse_value_slow_jets
#print axioms GlobalEmbedding.Continuation.actual_increment_gamma_row_slow_jets
