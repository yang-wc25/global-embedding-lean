import Probes.ActualIncrementAdaptedGeometry
import Probes.ActualIncrementSampleNormalTransfer
import Probes.ActualIncrementSampleReserve
import Probes.ActualIncrementSampleAdaptedConnection
import Probes.ActualIncrementSampleTransverseInverse
import Probes.ActualIncrementSampleCoefficients

/-! The complete SAME actual adapted geometry has the original six-field
constant on original samples. Genuine smoothness/injectivity domains stay
open and independent of the compact parameter sampling set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

private local instance rowFirstNormed (m N : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowFirstSpace (m N : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowHessianNormed (m N : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowHessianSpace (m N : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowPiNormed (m N : ℕ) : NormedAddCommGroup
    (Fin (m+1) → EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowPiSpace (m N : ℕ) : NormedSpace ℝ
    (Fin (m+1) → EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowFrameNormed (m N : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p} →L[ℝ]
      EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowFrameSpace (m N : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p} →L[ℝ]
      EuclideanSpace ℝ (Fin N)) := inferInstance

private theorem six_terms_le_abs_sum (a b c d e f : ℝ) :
    a ≤ |a|+|b|+|c|+|d|+|e|+|f| ∧ b ≤ |a|+|b|+|c|+|d|+|e|+|f| ∧
    c ≤ |a|+|b|+|c|+|d|+|e|+|f| ∧ d ≤ |a|+|b|+|c|+|d|+|e|+|f| ∧
    e ≤ |a|+|b|+|c|+|d|+|e|+|f| ∧ f ≤ |a|+|b|+|c|+|d|+|e|+|f| := by
  have ha := le_abs_self a
  have hb := le_abs_self b
  have hc := le_abs_self c
  have hd := le_abs_self d
  have he := le_abs_self e
  have hf := le_abs_self f
  have hna := abs_nonneg a
  have hnb := abs_nonneg b
  have hnc := abs_nonneg c
  have hnd := abs_nonneg d
  have hne := abs_nonneg e
  have hnf := abs_nonneg f
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

private local instance adaptedGeometryFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
private local instance adaptedGeometryT0Normed : NormedAddCommGroup (D →L[ℝ] Tdata) := inferInstance
private local instance adaptedGeometryT0Space : NormedSpace ℝ (D →L[ℝ] Tdata) := inferInstance

theorem actual_adapted_uniform_geometry_on_samples
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (he0 : ∀ p, e0 p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (he1 : ∀ p, e1 p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (U W S S0 : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hSU : S ⊆ U) (hS0W : S0 ⊆ W)
    (hcoord0 : ∀ z ∈ W, z.2 ∈ (e0 z.1).target)
    (hcoord : ∀ z ∈ U, z.2 ∈ (e1 z.1).target ∧ (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (hF0 : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hback : ContDiffOn ℝ ∞ (actualSourceChartTransition e1 e0) W)
    (hmap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (hsample : MapsTo (actualSourceChartTransition e0 e1) S S0)
    (hinj0 : ∀ z ∈ W, Function.Injective (fderiv ℝ (F z.1 ∘ (e0 z.1).symm) z.2))
    (ell c cT backBound MA MH : ℝ) (hell : 0 < ell)
    (hc : 0 < c) (hcT : 0 < cT) (hbackBoundPos : 0 < backBound)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ S0, ∀ v : D,
      c*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e0 z.1).symm) z.2 v‖^2)
    (hbackBound : ∀ z ∈ S0, ‖fderiv ℝ (actualSourceChartTransition e1 e0) z‖ ≤ backBound)
    (hTreserve : ∀ z ∈ U, ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (I := 𝓙) (F z.1) (hF z.1) (e1 z.1).symm z.2 v‖^2)
    (hAj : ∀ k ≤ j+1, ∀ z ∈ S0, ell^k*‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e0 y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ z ∈ S0, ell^k*‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e0 y.1).symm)) y.2) z‖ ≤ MH)
    (hphijet : ∀ k, 1 ≤ k → k ≤ j+2 → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k (actualSourceChartTransition e0 e1) z‖ ≤ T k) :
    let Mg := actualAdaptedUniformGeometryCost m N j T c cT backBound MA MH
    let G := fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ (e1 z.1).symm) z.2)
    let J := fun z : X => (normalSpace (I := 𝓙) (F z.1) ((e1 z.1).symm z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e1 z.1).symm z.2)
    let T0 := fun z : X => incrementsModeTransverseValue (F z.1) (e1 z.1).symm z.2
    let BR := fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e1 z.1).symm z.2 0 i : V)
    let A := fun z : X => incrementsModeComplexFirstOrderA (I := 𝓙) (F z.1) (hF z.1) (e1 z.1).symm z.2
    let B := fun z : X => incrementsModeComplexFirstOrderB (I := 𝓙) (F z.1) (hF z.1) (e1 z.1).symm z.2
    (ContDiffOn ℝ ∞ G U ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k G z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ J U ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k J z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ T0 U ∧ ∀ k ≤ j, ∀ z ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k T0 z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ BR U ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k BR z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ A U ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k A z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ B U ∧ ∀ k ≤ j, ∀ z ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k B z‖ ≤ Mg) := by
  dsimp only
  let ca := c/backBound^2
  let CA := actualFirstFrameTransferCost T (j+1)*MA
  let CQ := actualNormalChartTransferCost T j*actualIncrementSecondFormConstant m N j c MA MH
  let CB := ‖actualIncrementFirstRows m N‖*CQ
  let CC := ‖actualIncrementTransverseColumns m N‖*CQ
  let CG := 2^j*CA*slowInverseMajorant ca⁻¹ (2^j*CA^2) j
  let CJ := 2^j*CC*slowInverseMajorant cT⁻¹ (2^j*CC^2) j
  let CT := actualIncrementT0Constant m j ca CA CA
  let CGamma := actualIncrementGammaRowConstant m j ca CA CA
  have hca : 0 < ca := div_pos hc (sq_pos_of_pos hbackBoundPos)
  have hCA : 0 ≤ CA := mul_nonneg (actualFirstFrameTransferCost_nonneg T hT _) hMA
  have hCQ : 0 ≤ CQ := mul_nonneg (actualNormalChartTransferCost_nonneg T hT _)
    (actualIncrementSecondFormConstant_nonneg m N j hc hMA hMH)
  have hCB : 0 ≤ CB := mul_nonneg (actualIncrementFirstRows m N).opNorm_nonneg hCQ
  have hCC : 0 ≤ CC := mul_nonneg (actualIncrementTransverseColumns m N).opNorm_nonneg hCQ
  have hCJ : 0 ≤ CJ := mul_nonneg (mul_nonneg (by positivity) hCC)
    (slowInverseMajorant_nonneg (inv_nonneg.mpr hcT.le) (by positivity) j)
  have hCT : 0 ≤ CT := actualIncrementT0Constant_nonneg m j hca hCA hCA
  have hCGamma : 0 ≤ CGamma := actualIncrementGammaRowConstant_nonneg m j hca hCA hCA
  have hA0 := (incrementsJointSpatialJets_bridge _ W hW hF0).2.1
  have hH0 := (incrementsJointSpatialJets_bridge _ W hW hF0).2.2
  have hr1 := actual_adapted_first_frame_reserve_on_samples F e0 e1 U W S S0 hU hW hSU hF0
    hphi hback hmap hsample hcoord c backBound hc hbackBoundPos hreserve hbackBound
  have hinj1 := actual_adapted_first_frame_injective F e0 e1 U W hU hW hF0
    hphi hback hmap hcoord hinj0
  have hinjT : ∀ z ∈ U, Function.Injective (incrementsModeAmbientTransverseFrame
      (I := 𝓙) (F z.1) (hF z.1) (e1 z.1).symm z.2) := by
    intro z hz
    exact actual_frame_injective_of_reserve _ cT hcT (hTreserve z hz)
  obtain ⟨_,hA1,_,hA1b⟩ := actual_first_frame_hessian_transferred_on_samples T hT j F e0 e1
    U W S S0 hU hW hSU hS0W hF0 hphi hmap hsample (fun z hz => (hcoord z hz).2) ell MA hell hMA hAj hphijet
  obtain ⟨hQ,hQb⟩ := actual_normal_hessian_transferred_on_samples T hT j F hF e0 e1 he0
    U W S S0 hU hW hSU hS0W hcoord0 hF0 hA0 hH0 hphi hmap hsample hinj0 hcoord ell c MA MH hell hc hMA hMH hreserve
    (fun k hk z hz => hAj k (by omega) z hz) hHj
    (fun k hk hkj z hz => hphijet k hk (by omega) z hz)
  obtain ⟨hBR,hFrame⟩ := actual_true_geometry_from_normal_hessian_on_samples F hF e1 he1 U S hU hSU
    (fun z hz => (hcoord z hz).1) hQ j ell CQ hell.le hQb
  have hG := actual_freeGramRightInverse_slow_jets_on_samples _ U S hU hSU hA1 hinj1 j ell ca CA hell hca hCA hr1
    (fun k hk z hz => (hA1b k hk z hz).1)
  have hJ := actual_original_transverse_J_on_samples F hF (fun p x => (e1 p).symm x)
    U S hU hSU hFrame.1 hinjT j ell cT CC hell hcT hCC (fun z hz => hTreserve z (hSU hz)) hFrame.2
  obtain ⟨hT0,hGamma⟩ := actual_adapted_T0_gamma_on_samples T hT j F e0 e1 U W S S0 hU hW hSU hS0W
    hF0 hphi hmap hsample hinj1 (fun z hz => (hcoord z hz).2) ell MA ca hell hMA hca hr1 hAj hphijet
  obtain ⟨hA,hB⟩ := actual_increment_complex_coefficients_on_samples F hF e1 U S hU hSU j
    ell CB CJ CT CGamma hell hCB hCJ hCT hCGamma hBR.1 hJ.1 hT0.1 hGamma.1
    hBR.2 hJ.2 hT0.2 hGamma.2
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := six_terms_le_abs_sum CG CJ CT CB
    (actualAdaptedComplexACost m N j CB CJ) (actualAdaptedComplexBCost m N j CB CJ CT CGamma)
  exact ⟨⟨hG.1,fun k hk z hz => (hG.2 k hk z hz).trans h0⟩,
    ⟨hJ.1,fun k hk z hz => (hJ.2 k hk z hz).trans h1⟩,
    ⟨hT0.1,fun k hk z hz => (hT0.2 k hk z hz).trans h2⟩,
    ⟨hBR.1,fun k hk z hz => (hBR.2 k hk z hz).trans h3⟩,
    ⟨hA.1,fun k hk z hz => (hA.2 k hk z hz).trans h4⟩,
    ⟨hB.1,fun k hk z hz => (hB.2 k hk z hz).trans h5⟩⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_adapted_uniform_geometry_on_samples
