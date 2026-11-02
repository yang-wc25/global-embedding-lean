import Smoothing.ParameterRound2GlobalObservedError
import Smoothing.ParameterRound2GlobalCorrectionDifferenceSum

/-! Same-input full-joint difference of the literal global observed error.
The actual vector corrections are grouped by the original phase before
projection. This retains all subordinate cross terms and introduces no
mean/error estimate as a premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem parameterRound2_actual_globalObservedError_difference_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length j : ℕ) (ν : Λ) (e : OpenPartialHomeomorph M D) (r : Fin (m+1)) (coord : Fin N)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (tau ell Cv CP CQ Mphi Delta : ℝ) (hell : 0 < ell) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hDelta : 0 ≤ Delta) (hCv : 0 ≤ Cv) (hCP : 0 ≤ CP) (hCQ : 0 ≤ CQ) (hMphi : 0 ≤ Mphi)
    (hb : ContDiffOn ℝ ∞ (fun z : X => incrementsGlobalPrimaryB F g input ν (z.1,e.symm z.2)) O)
    (hbbar : ContDiffOn ℝ ∞ (fun z : X => incrementsGlobalPrimaryB F g inputbar ν (z.1,e.symm z.2)) O)
    (hn : ContDiffOn ℝ ∞ (fun z : X => g.normal ν (z.1,e.symm z.2)) O)
    (hphi : ContDiffOn ℝ ∞ (fun z : X => g.phase ν (z.1,e.symm z.2)) O)
    (hP : ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      parameterRound2_globalCorrection F hF g input length tau true ν β (z.1,e.symm z.2)) O)
    (hQ : ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      parameterRound2_globalCorrection F hF g input length tau false ν β (z.1,e.symm z.2)) O)
    (hPbar : ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      parameterRound2_globalCorrection F hF g inputbar length tau true ν β (z.1,e.symm z.2)) O)
    (hQbar : ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      parameterRound2_globalCorrection F hF g inputbar length tau false ν β (z.1,e.symm z.2)) O)
    (hVb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => incrementsGlobalPrimaryFree F g input tau ν (y.1,e.symm y.2) -
        incrementsGlobalPrimaryFree F g inputbar tau ν (y.1,e.symm y.2)) z‖ ≤ Cv*tau*Delta)
    (hPb : ∀ k ≤ j+1, ∀ z ∈ S, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun y : X => (∑ β, parameterRound2_globalCorrection F hF g input length tau true ν β
        (y.1,e.symm y.2)) - ∑ β, parameterRound2_globalCorrection F hF g inputbar length tau true ν β
          (y.1,e.symm y.2)) z‖ ≤ CP*tau^2*Delta)
    (hQb : ∀ k ≤ j+1, ∀ z ∈ S, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun y : X => (∑ β, parameterRound2_globalCorrection F hF g input length tau false ν β
        (y.1,e.symm y.2)) - ∑ β, parameterRound2_globalCorrection F hF g inputbar length tau false ν β
          (y.1,e.symm y.2)) z‖ ≤ CQ*tau^2*Delta)
    (hgrad : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fun x => g.phase ν (y.1,e.symm x)) y.2
        (EuclideanSpace.single r 1)) z‖ ≤ Mphi) :
    let err := fun z : X => incrementsGlobalObservedError F hF g input length tau e z.1 z.2 ν r coord -
      incrementsGlobalObservedError F hF g inputbar length tau e z.1 z.2 ν r coord
    ContDiffOn ℝ ∞ err O ∧ ∀ k ≤ j, ∀ z ∈ S,
      ell^k * ‖iteratedFDeriv ℝ k err z‖ ≤
        actualJointPrimaryErrorCost j (EuclideanSpace.single r 1) coord Cv
          (actualJointCorrectionSumCost N 1 coord CP CQ) Mphi * (tau/ell)*Delta := by
  intro err
  let b := fun z : X => incrementsGlobalPrimaryB F g input ν (z.1,e.symm z.2)
  let bbar := fun z : X => incrementsGlobalPrimaryB F g inputbar ν (z.1,e.symm z.2)
  let normal := fun z : X => g.normal ν (z.1,e.symm z.2)
  let phi := fun z : X => g.phase ν (z.1,e.symm z.2)
  let P := fun β (z : X) => parameterRound2_globalCorrection F hF g input length tau true ν β (z.1,e.symm z.2)
  let Q := fun β (z : X) => parameterRound2_globalCorrection F hF g input length tau false ν β (z.1,e.symm z.2)
  let Pbar := fun β (z : X) => parameterRound2_globalCorrection F hF g inputbar length tau true ν β (z.1,e.symm z.2)
  let Qbar := fun β (z : X) => parameterRound2_globalCorrection F hF g inputbar length tau false ν β (z.1,e.symm z.2)
  let C := fun (P Q : Β → X → V) (z : X) => ∑ β,
    (incrementsFreeComplexCoordinate coord (P β z)+Complex.I • incrementsFreeComplexCoordinate coord (Q β z))
  have hPd : ContDiffOn ℝ ∞ (fun z => ∑ β, (P β z-Pbar β z)) O :=
    ContDiffOn.sum (fun β _ => (hP β).sub (hPbar β))
  have hQd : ContDiffOn ℝ ∞ (fun z => ∑ β, (Q β z-Qbar β z)) O :=
    ContDiffOn.sum (fun β _ => (hQ β).sub (hQbar β))
  have hPdb : ∀ k ≤ j+1, ∀ z ∈ S,
      ell^(k+1)*‖iteratedFDeriv ℝ k (fun y => ∑ β, (P β y-Pbar β y)) z‖ ≤ (CP*Delta)*tau^2 := by
    simp only [Finset.sum_sub_distrib]
    intro k hk z hz
    exact (hPb k hk z hz).trans_eq (by ring)
  have hQdb : ∀ k ≤ j+1, ∀ z ∈ S,
      ell^(k+1)*‖iteratedFDeriv ℝ k (fun y => ∑ β, (Q β y-Qbar β y)) z‖ ≤ (CQ*Delta)*tau^2 := by
    simp only [Finset.sum_sub_distrib]
    intro k hk z hz
    exact (hQb k hk z hz).trans_eq (by ring)
  have hC := parameterRound2_complex_correction_sum_from_vector_sums
    (fun β z => P β z-Pbar β z) (fun β z => Q β z-Qbar β z) coord O S hO hSO hPd hQd
    (j+1) ell tau (CP*Delta) (CQ*Delta) hell.le (mul_nonneg hCP hDelta) (mul_nonneg hCQ hDelta) hPdb hQdb
  have hCeq : (fun z => ∑ β, (incrementsFreeComplexCoordinate coord (P β z-Pbar β z)+
      Complex.I • incrementsFreeComplexCoordinate coord (Q β z-Qbar β z))) =
      fun z => C P Q z-C Pbar Qbar z := by
    funext z
    dsimp only [C]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro β hβ
    simp only [map_sub,smul_sub]
    abel
  have hCd : ∀ k ≤ j+1, ∀ z ∈ S,
      ell^(k+1)*‖iteratedFDeriv ℝ k (fun y => C P Q y-C Pbar Qbar y) z‖ ≤
        actualJointCorrectionSumCost N 1 coord CP CQ*tau^2*Delta := by
    rw [hCeq] at hC
    intro k hk z hz
    exact (hC.2 k hk z hz).trans_eq (by unfold actualJointCorrectionSumCost; ring)
  have hCz := actualJointCorrectionSumCost_nonneg 1 coord hCP hCQ
  have hVF : ∀ k ≤ j+1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => (Real.sqrt 2*1*tau*b y) • normal y -
        (Real.sqrt 2*1*tau*bbar y) • normal y) z‖ ≤ Cv*tau*Delta := by
    simpa only [b,bbar,normal,mul_one,incrementsGlobalPrimaryFree] using hVb
  have hout := actual_joint_primary_error_difference_slow_jets b bbar phi normal P Q Pbar Qbar
    (EuclideanSpace.single r 1) coord O S hO hSO hb hbbar hn hphi hP hQ hPbar hQbar j ell tau Cv
    (actualJointCorrectionSumCost N 1 coord CP CQ) Mphi Delta hell htau htaul hCv hCz hMphi hDelta
    hVF hCd hgrad
  simpa only [err,b,bbar,normal,phi,P,Q,Pbar,Qbar,parameterRound2_globalCorrection,
    Bool.false_eq_true,ite_false,ite_true,sub_zero,incrementsGlobalObservedError] using hout

#print axioms parameterRound2_actual_globalObservedError_difference_slow_jets
end GlobalEmbedding.Continuation
