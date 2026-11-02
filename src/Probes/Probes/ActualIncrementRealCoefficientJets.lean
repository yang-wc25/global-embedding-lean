import Probes.ActualIncrementGeometricJets

/-!
# Real coefficients of the original finite differential solver from geometry

The first-order A/B fields below are exactly `incrementsModeFirstOrderA/B`.
Their joint smoothness and weighted jets follow from the same actual first
and Hessian fields, and fixed first/transverse reserves. No A/B/J/T0 budget
appears among the primitive assumptions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

private local instance realDDNormed (m : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance realDDSpace (m : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance realZNormed (m : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2} →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance realZSpace (m : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2} →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance realANormed (m : ℕ) : NormedAddCommGroup
    ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance realASpace (m : ℕ) : NormedSpace ℝ
    ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1))) := inferInstance

def actualIncrementJetComposition (m : ℕ) :
    (EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2} →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
      ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
        EuclideanSpace ℝ (Fin (m+1))) :=
  (ContinuousLinearMap.compL ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)))
    (EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2})
    (EuclideanSpace ℝ (Fin (m+1)))).flip incrementsModeTransverseJet

def actualIncrementRowJConstant (m N j : ℕ) (c cT MA MH : ℝ) : ℝ :=
  2^j * (‖actualIncrementFullRowPairing m N‖ * actualIncrementFirstRowsConstant m N j c MA MH) *
    actualIncrementJConstant m N j c cT MA MH

def actualIncrementRealAConstant (m N j : ℕ) (c cT MA MH : ℝ) : ℝ :=
  ‖actualIncrementPrincipalFirstOrderA m‖ +
    ‖actualIncrementJetComposition m‖ * actualIncrementRowJConstant m N j c cT MA MH

def actualIncrementRealBConstant (m N j : ℕ) (c cT MA MH : ℝ) : ℝ :=
  actualIncrementGammaRowConstant m j c MA MH +
    2^j * actualIncrementRowJConstant m N j c cT MA MH * actualIncrementT0Constant m j c MA MH

theorem actual_increment_slow_const_jet_bound
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (v : Y) (k : ℕ) (ell : ℝ) (x : X) :
    ell^k * ‖iteratedFDeriv ℝ k (fun _ : X => v) x‖ ≤ ‖v‖ := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [iteratedFDeriv_const_of_ne hk]
    simp

theorem actual_increment_slow_sub_jet_bound
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f g : X → Y) (k : ℕ) (ell Mf Mg : ℝ) (hell : 0 ≤ ell) (x : X)
    (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x)
    (hfb : ell^k * ‖iteratedFDeriv ℝ k f x‖ ≤ Mf)
    (hgb : ell^k * ‖iteratedFDeriv ℝ k g x‖ ≤ Mg) :
    ell^k * ‖iteratedFDeriv ℝ k (fun y => f y - g y) x‖ ≤ Mf + Mg := by
  rw [fun_iteratedFDeriv_sub_apply hf hg]
  calc
    _ ≤ ell^k * (‖iteratedFDeriv ℝ k f x‖ + ‖iteratedFDeriv ℝ k g x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (pow_nonneg hell k)
    _ = ell^k * ‖iteratedFDeriv ℝ k f x‖ + ell^k * ‖iteratedFDeriv ℝ k g x‖ := by ring
    _ ≤ Mf + Mg := add_le_add hfb hgb

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

/-- Primitive actual geometric jets supply both real original first-order
coefficient fields on the same open joint domain and at the same slow scale. -/
theorem actual_increment_real_coefficients_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hA : ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2) O)
    (hH : ContDiffOn ℝ ∞ (fun z : X =>
      fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2) O)
    (j : ℕ) (ell c cT MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c) (hcT : 0 < cT)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ O, ∀ v : D,
      c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hTreserve : ∀ z ∈ O, ∀ v : Tdata,
      cT * ‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame (I := 𝓙)
        (F z.1) (hF z.1) (e z.1).symm z.2 v‖^2)
    (hAj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH) :
    (ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeFirstOrderA (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) O ∧
      ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k (fun y : X =>
        incrementsModeFirstOrderA (I := 𝓙) (F y.1) (hF y.1) (e y.1).symm y.2) z‖ ≤
          actualIncrementRealAConstant m N j c cT MA MH) ∧
    (ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeFirstOrderB (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) O ∧
      ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k (fun y : X =>
        incrementsModeFirstOrderB (I := 𝓙) (F y.1) (hF y.1) (e y.1).symm y.2) z‖ ≤
          actualIncrementRealBConstant m N j c cT MA MH) := by
  let B : X → Fin (m+1) → V := fun z i =>
    (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 0 i : V)
  let J : X → Tdata →L[ℝ] V := fun z =>
    (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2)
  let T : X → D →L[ℝ] Tdata := fun z => incrementsModeTransverseValue (F z.1) (e z.1).symm z.2
  let G : X → D →L[ℝ] D := fun z => actualIncrementFullRowPairing m (m+1)
    (fun i => incrementsModeGamma (F z.1) (e z.1).symm z.2 0 i)
  let CB := actualIncrementFirstRowsConstant m N j c MA MH
  let CJ := actualIncrementJConstant m N j c cT MA MH
  let CT := actualIncrementT0Constant m j c MA MH
  let CG := actualIncrementGammaRowConstant m j c MA MH
  let CZ := actualIncrementRowJConstant m N j c cT MA MH
  have hCB : 0 ≤ CB := actualIncrementFirstRowsConstant_nonneg m N j hc hMA hMH
  have hCJ : 0 ≤ CJ := actualIncrementJConstant_nonneg m N j hc hcT hMA hMH
  have hCT : 0 ≤ CT := actualIncrementT0Constant_nonneg m j hc hMA hMH
  have hCG : 0 ≤ CG := actualIncrementGammaRowConstant_nonneg m j hc hMA hMH
  have hCZ : 0 ≤ CZ := mul_nonneg
    (mul_nonneg (by positivity) (mul_nonneg (actualIncrementFullRowPairing m N).opNorm_nonneg hCB)) hCJ
  obtain ⟨hB,hBb⟩ := actual_increment_first_rows_slow_jets F hF e he O hO hcoord
    hA hH j ell c MA MH hell hc hMA hMH hreserve hAj hHj
  obtain ⟨hJ,hJb⟩ := actual_increment_transverse_J_from_primitive_jets F hF e he O hO hcoord
    hA hH j ell c MA MH hell hc hMA hMH hreserve hAj hHj cT hcT hTreserve
  obtain ⟨hT,hTb⟩ := actual_increment_transverse_value_slow_jets F hF e he O hO hcoord hA hH
    j ell c MA MH hell hc hMA hMH hreserve hAj hHj
  obtain ⟨hG,hGb⟩ := actual_increment_gamma_row_slow_jets F hF e he O hO hcoord hA hH
    j ell c MA MH hell hc hMA hMH hreserve hAj hHj
  let L := actualIncrementFullRowPairing m N
  let P : X → V →L[ℝ] D := L ∘ B
  let Z : X → Tdata →L[ℝ] D := fun z => (P z).comp (J z)
  have hP : ContDiffOn ℝ ∞ P O := L.contDiff.comp_contDiffOn hB
  have hPb : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k P z‖ ≤ ‖L‖ * CB := by
    intro k hk z hz
    exact slow_linear_jet_bound L O hO B hB k ell CB hell.le z hz (hBb k hk z hz)
  have hZ : ContDiffOn ℝ ∞ Z O := hP.clm_comp hJ
  have hZb : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k Z z‖ ≤ CZ := by
    intro k hk z hz
    have hb := slow_bilinear_jet_bound (ContinuousLinearMap.compL ℝ Tdata V D)
      (ContinuousLinearMap.norm_compL_le ℝ Tdata V D) O hO P J hP hJ k ell
      (‖L‖ * CB) CJ hell.le (mul_nonneg L.opNorm_nonneg hCB) z hz
      (fun r hr => hPb r (hr.trans hk) z hz) (fun r hr => hJb r (hr.trans hk) z hz)
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hk) (mul_nonneg L.opNorm_nonneg hCB)) hCJ)
  let Lj := actualIncrementJetComposition m
  let W : X → (D →L[ℝ] D) →L[ℝ] D := Lj ∘ Z
  have hW : ContDiffOn ℝ ∞ W O := Lj.contDiff.comp_contDiffOn hZ
  have hWb : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k W z‖ ≤ ‖Lj‖ * CZ := by
    intro k hk z hz
    exact slow_linear_jet_bound Lj O hO Z hZ k ell CZ hell.le z hz (hZb k hk z hz)
  let ZT : X → D →L[ℝ] D := fun z => (Z z).comp (T z)
  have hZT : ContDiffOn ℝ ∞ ZT O := hZ.clm_comp hT
  have hZTb : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k ZT z‖ ≤ 2^j * CZ * CT := by
    intro k hk z hz
    have hb := slow_bilinear_jet_bound (ContinuousLinearMap.compL ℝ D Tdata D)
      (ContinuousLinearMap.norm_compL_le ℝ D Tdata D) O hO Z T hZ hT k ell CZ CT hell.le hCZ z hz
      (fun r hr => hZb r (hr.trans hk) z hz) (fun r hr => hTb r (hr.trans hk) z hz)
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hk) hCZ) hCT)
  have hAe : (fun z : X => incrementsModeFirstOrderA (I := 𝓙)
      (F z.1) (hF z.1) (e z.1).symm z.2) = fun z => actualIncrementPrincipalFirstOrderA m - W z :=
    funext fun z => actual_increment_first_order_A_eq (F z.1) (hF z.1) (e z.1).symm z.2
  have hBe : (fun z : X => incrementsModeFirstOrderB (I := 𝓙)
      (F z.1) (hF z.1) (e z.1).symm z.2) = fun z => -G z - ZT z :=
    funext fun z => actual_increment_first_order_B_eq (F z.1) (hF z.1) (e z.1).symm z.2
  rw [hAe,hBe]
  constructor
  · refine ⟨contDiffOn_const.sub hW, ?_⟩
    intro k hk z hz
    exact actual_increment_slow_sub_jet_bound (fun _ : X => actualIncrementPrincipalFirstOrderA m) W
      k ell ‖actualIncrementPrincipalFirstOrderA m‖ (‖Lj‖ * CZ) hell.le z contDiffAt_const
      ((hW.contDiffAt (hO.mem_nhds hz)).of_le (by simp))
      (actual_increment_slow_const_jet_bound _ k ell z) (hWb k hk z hz)
  · refine ⟨hG.neg.sub hZT, ?_⟩
    intro k hk z hz
    have hneg : ell^k * ‖iteratedFDeriv ℝ k (fun y => -G y) z‖ ≤ CG := by
      change ell^k * ‖iteratedFDeriv ℝ k (-G) z‖ ≤ CG
      rw [iteratedFDeriv_neg_apply, norm_neg]
      exact hGb k hk z hz
    exact actual_increment_slow_sub_jet_bound (fun y => -G y) ZT k ell CG (2^j * CZ * CT)
      hell.le z (((hG.neg).contDiffAt (hO.mem_nhds hz)).of_le (by simp))
      ((hZT.contDiffAt (hO.mem_nhds hz)).of_le (by simp)) hneg (hZTb k hk z hz)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_real_coefficients_slow_jets
