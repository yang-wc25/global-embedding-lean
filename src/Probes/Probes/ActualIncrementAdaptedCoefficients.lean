import Probes.ActualIncrementComplexCoefficientJets
import Probes.ActualAdaptedConnectionJets

/-! The actual A/B solver coefficients with the geometrically correct scales:
true B rows and J have shift zero, Gamma/T0 and the value coefficient B have
shift one. The final adapted geometry producer discharges all profiles here
from original map jets, actual chart transitions and the two genuine reserves. -/

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

private local instance complexDDNormed (m : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance complexDDSpace (m : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance complexDCNormed (m : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexDCSpace (m : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexCCNormed (m : ℕ) : NormedAddCommGroup ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexCCSpace (m : ℕ) : NormedSpace ℝ ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexRealANormed (m : ℕ) : NormedAddCommGroup ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance complexRealASpace (m : ℕ) : NormedSpace ℝ ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance complexMidANormed (m : ℕ) : NormedAddCommGroup ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexMidASpace (m : ℕ) : NormedSpace ℝ ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexComplexANormed (m : ℕ) : NormedAddCommGroup ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexComplexASpace (m : ℕ) : NormedSpace ℝ ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexRealJetNormed (m : ℕ) : NormedAddCommGroup ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)))) := inferInstance
private local instance complexRealJetSpace (m : ℕ) : NormedSpace ℝ ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)))) := inferInstance

def actualAdaptedRowJCost (m N j : ℕ) (MB MJ : ℝ) : ℝ :=
  2^j*(‖actualIncrementFullRowPairing m N‖*MB)*MJ

def actualAdaptedRealACost (m N j : ℕ) (MB MJ : ℝ) : ℝ :=
  ‖actualIncrementPrincipalFirstOrderA m‖ +
    ‖actualIncrementJetComposition m‖*actualAdaptedRowJCost m N j MB MJ

def actualAdaptedRealBCost (m N j : ℕ) (MB MJ MT MGamma : ℝ) : ℝ :=
  MGamma + 2^j*actualAdaptedRowJCost m N j MB MJ*MT

def actualAdaptedComplexACost (m N j : ℕ) (MB MJ : ℝ) : ℝ :=
  ‖actualIncrementComplexAMap m‖*actualAdaptedRealACost m N j MB MJ

def actualAdaptedComplexBCost (m N j : ℕ) (MB MJ MT MGamma : ℝ) : ℝ :=
  ‖actualIncrementComplexBMap m‖*actualAdaptedRealBCost m N j MB MJ MT MGamma

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
theorem actual_increment_real_coefficients_from_split_geometry
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (O : Set X) (hO : IsOpen O) (j : ℕ)
    (ell MB MJ MT MGamma : ℝ) (hell : 0 < ell)
    (hMB : 0 ≤ MB) (hMJ : 0 ≤ MJ) (hMT : 0 ≤ MT) (hMGamma : 0 ≤ MGamma)
    (hB : ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2)) O)
    (hT : ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (e z.1).symm z.2) O)
    (hG : ContDiffOn ℝ ∞ (fun z : X => actualIncrementFullRowPairing m (m+1)
      (fun i => incrementsModeGamma (F z.1) (e z.1).symm z.2 0 i)) O)
    (hBb : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun z : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 0 i : V)) z‖ ≤ MB)
    (hJb : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun z : X => (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2)) z‖ ≤ MJ)
    (hTb : ∀ k ≤ j, ∀ z ∈ O, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun z : X => incrementsModeTransverseValue (F z.1) (e z.1).symm z.2) z‖ ≤ MT)
    (hGb : ∀ k ≤ j, ∀ z ∈ O, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun z : X => actualIncrementFullRowPairing m (m+1)
        (fun i => incrementsModeGamma (F z.1) (e z.1).symm z.2 0 i)) z‖ ≤ MGamma) :
    (ContDiffOn ℝ ∞ (fun z : X => incrementsModeFirstOrderA (I := 𝓙)
      (F z.1) (hF z.1) (e z.1).symm z.2) O ∧
      ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k (fun z : X =>
        incrementsModeFirstOrderA (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) z‖ ≤
          actualAdaptedRealACost m N j MB MJ) ∧
    (ContDiffOn ℝ ∞ (fun z : X => incrementsModeFirstOrderB (I := 𝓙)
      (F z.1) (hF z.1) (e z.1).symm z.2) O ∧
      ∀ k ≤ j, ∀ z ∈ O, ell^(k+1) * ‖iteratedFDeriv ℝ k (fun z : X =>
        incrementsModeFirstOrderB (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) z‖ ≤
          actualAdaptedRealBCost m N j MB MJ MT MGamma) := by
  let B : X → Fin (m+1) → V := fun z i =>
    (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 0 i : V)
  let J : X → Tdata →L[ℝ] V := fun z =>
    (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2)
  let T : X → D →L[ℝ] Tdata := fun z => incrementsModeTransverseValue (F z.1) (e z.1).symm z.2
  let G : X → D →L[ℝ] D := fun z => actualIncrementFullRowPairing m (m+1)
    (fun i => incrementsModeGamma (F z.1) (e z.1).symm z.2 0 i)
  let CB := MB
  let CJ := MJ
  let CT := MT
  let CG := MGamma
  let CZ := actualAdaptedRowJCost m N j MB MJ
  have hCB : 0 ≤ CB := hMB
  have hCJ : 0 ≤ CJ := hMJ
  have hCT : 0 ≤ CT := hMT
  have hCG : 0 ≤ CG := hMGamma
  have hCZ : 0 ≤ CZ := mul_nonneg
    (mul_nonneg (by positivity) (mul_nonneg (actualIncrementFullRowPairing m N).opNorm_nonneg hCB)) hCJ
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
  have hZTb : ∀ k ≤ j, ∀ z ∈ O, ell^(k+1) * ‖iteratedFDeriv ℝ k ZT z‖ ≤ 2^j * CZ * CT := by
    intro k hk z hz
    have hT0 : ∀ r ≤ k, ell^r * ‖iteratedFDeriv ℝ r T z‖ ≤ CT/ell := by
      intro r hr
      apply (le_div_iff₀ hell).2
      simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using hTb r (hr.trans hk) z hz
    have hb := slow_bilinear_jet_bound (ContinuousLinearMap.compL ℝ D Tdata D)
      (ContinuousLinearMap.norm_compL_le ℝ D Tdata D) O hO Z T hZ hT k ell CZ (CT/ell) hell.le hCZ z hz
      (fun r hr => hZb r (hr.trans hk) z hz) hT0
    have hm := hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hk) hCZ) (div_nonneg hCT hell.le))
    calc
      _ = (ell^k * ‖iteratedFDeriv ℝ k ZT z‖)*ell := by rw [pow_succ]; ring
      _ ≤ (2^j*CZ*(CT/ell))*ell := mul_le_mul_of_nonneg_right hm hell.le
      _ = _ := by field_simp
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
    have hneg : ell^(k+1) * ‖iteratedFDeriv ℝ k (fun y => -G y) z‖ ≤ CG := by
      change ell^(k+1) * ‖iteratedFDeriv ℝ k (-G) z‖ ≤ CG
      rw [iteratedFDeriv_neg_apply,norm_neg]
      exact hGb k hk z hz
    rw [fun_iteratedFDeriv_sub_apply (f := fun y => -G y) (g := ZT)
      (((hG.neg).contDiffAt (hO.mem_nhds hz)).of_le (by simp))
      ((hZT.contDiffAt (hO.mem_nhds hz)).of_le (by simp))]
    calc
      _ ≤ ell^(k+1) * (‖iteratedFDeriv ℝ k (fun y => -G y) z‖ + ‖iteratedFDeriv ℝ k ZT z‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (pow_nonneg hell.le _)
      _ = ell^(k+1) * ‖iteratedFDeriv ℝ k (fun y => -G y) z‖ +
          ell^(k+1) * ‖iteratedFDeriv ℝ k ZT z‖ := mul_add _ _ _
      _ ≤ CG + 2^j*CZ*CT := add_le_add hneg (hZTb k hk z hz)
      _ = _ := rfl

theorem actual_increment_complex_coefficients_from_split_geometry
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (O : Set X) (hO : IsOpen O) (j : ℕ)
    (ell MB MJ MT MGamma : ℝ) (hell : 0 < ell)
    (hMB : 0 ≤ MB) (hMJ : 0 ≤ MJ) (hMT : 0 ≤ MT) (hMGamma : 0 ≤ MGamma)
    (hB : ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2)) O)
    (hT : ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (e z.1).symm z.2) O)
    (hG : ContDiffOn ℝ ∞ (fun z : X => actualIncrementFullRowPairing m (m+1)
      (fun i => incrementsModeGamma (F z.1) (e z.1).symm z.2 0 i)) O)
    (hBb : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun z : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 0 i : V)) z‖ ≤ MB)
    (hJb : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun z : X => (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2)) z‖ ≤ MJ)
    (hTb : ∀ k ≤ j, ∀ z ∈ O, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun z : X => incrementsModeTransverseValue (F z.1) (e z.1).symm z.2) z‖ ≤ MT)
    (hGb : ∀ k ≤ j, ∀ z ∈ O, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun z : X => actualIncrementFullRowPairing m (m+1)
        (fun i => incrementsModeGamma (F z.1) (e z.1).symm z.2 0 i)) z‖ ≤ MGamma) :
    (ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (I := 𝓙)
      (F z.1) (hF z.1) (e z.1).symm z.2) O ∧
      ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k (fun z : X =>
        incrementsModeComplexFirstOrderA (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) z‖ ≤
          actualAdaptedComplexACost m N j MB MJ) ∧
    (ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (I := 𝓙)
      (F z.1) (hF z.1) (e z.1).symm z.2) O ∧
      ∀ k ≤ j, ∀ z ∈ O, ell^(k+1) * ‖iteratedFDeriv ℝ k (fun z : X =>
        incrementsModeComplexFirstOrderB (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) z‖ ≤
          actualAdaptedComplexBCost m N j MB MJ MT MGamma) := by
  obtain ⟨hRA,hRB⟩ := actual_increment_real_coefficients_from_split_geometry
    F hF e O hO j ell MB MJ MT MGamma hell hMB hMJ hMT hMGamma hB hJ hT hG hBb hJb hTb hGb
  let A := fun z : X => incrementsModeFirstOrderA (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2
  let B := fun z : X => incrementsModeFirstOrderB (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2
  let LA := actualIncrementComplexAMap m
  let LB := actualIncrementComplexBMap m
  have hAe : (fun z : X => incrementsModeComplexFirstOrderA (I := 𝓙)
      (F z.1) (hF z.1) (e z.1).symm z.2) = LA ∘ A :=
    funext fun z => actual_increment_complex_A_eq (F z.1) (hF z.1) (e z.1) z.2
  have hBe : (fun z : X => incrementsModeComplexFirstOrderB (I := 𝓙)
      (F z.1) (hF z.1) (e z.1).symm z.2) = LB ∘ B :=
    funext fun z => actual_increment_complex_B_eq (F z.1) (hF z.1) (e z.1) z.2
  rw [hAe,hBe]
  constructor
  · refine ⟨LA.contDiff.comp_contDiffOn hRA.1, ?_⟩
    intro k hk z hz
    exact slow_linear_jet_bound LA O hO A hRA.1 k ell
      (actualAdaptedRealACost m N j MB MJ) hell.le z hz (hRA.2 k hk z hz)
  · refine ⟨LB.contDiff.comp_contDiffOn hRB.1, ?_⟩
    intro k hk z hz
    exact actual_slow_shift_one_linear_jet LB B O hO hRB.1 k ell
      (actualAdaptedRealBCost m N j MB MJ MT MGamma) hell z hz (hRB.2 k hk z hz)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_real_coefficients_from_split_geometry

#print axioms GlobalEmbedding.Continuation.actual_increment_complex_coefficients_from_split_geometry
