import Smoothing.ParameterRound2GlobalCorrectionRegularity
import Smoothing.ParameterRound2GlobalCorrectionSum
import Probes.ActualIncrementJointCorrectionSum

/-!
# The literal global observed error from the SAME transported corrections

All subordinate reconstructions are first transported through their own
charts. The two vector sums are then projected to the original complex
coefficient, retaining same-phase cross terms. This consumer uses those
actual shifted Rsum budgets, supplied by GlobalCorrectionSum, to derive the
literal GlobalObservedError with its tau/ell gain and full parameter jets.
It assumes no primary-error or mean budget.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

theorem parameterRound2_complex_correction_sum_from_vector_sums
    {X A : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype A] {N : ℕ}
    (P Q : A → X → EuclideanSpace ℝ (Fin N)) (coord : Fin N)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hP : ContDiffOn ℝ ∞ (fun z => ∑ a, P a z) O)
    (hQ : ContDiffOn ℝ ∞ (fun z => ∑ a, Q a z) O)
    (j : ℕ) (ell tau CP CQ : ℝ) (hell : 0 ≤ ell) (hCP : 0 ≤ CP) (hCQ : 0 ≤ CQ)
    (hPb : ∀ k ≤ j, ∀ z ∈ S,
      ell^(k+1)*‖iteratedFDeriv ℝ k (fun y => ∑ a, P a y) z‖ ≤ CP*tau^2)
    (hQb : ∀ k ≤ j, ∀ z ∈ S,
      ell^(k+1)*‖iteratedFDeriv ℝ k (fun y => ∑ a, Q a y) z‖ ≤ CQ*tau^2) :
    let C := fun z => ∑ a, (incrementsFreeComplexCoordinate coord (P a z) +
      Complex.I • incrementsFreeComplexCoordinate coord (Q a z))
    ContDiffOn ℝ ∞ C O ∧ ∀ k ≤ j, ∀ z ∈ S,
      ell^(k+1)*‖iteratedFDeriv ℝ k C z‖ ≤ actualJointCorrectionSumCost N 1 coord CP CQ*tau^2 := by
  intro C
  have h := actual_joint_correction_sum_slow_jets j 1 coord (A := Unit) (by simp)
    (fun _ z => ∑ a, P a z) (fun _ z => ∑ a, Q a z) O S hO hSO (fun _ => hP) (fun _ => hQ)
    ell tau CP CQ hell hCP hCQ (fun _ => hPb) (fun _ => hQb)
  have heq : (fun z => ∑ _a : Unit,
      (incrementsFreeComplexCoordinate coord (∑ a, P a z) +
        Complex.I • incrementsFreeComplexCoordinate coord (∑ a, Q a z))) = C := by
    funext z
    simp [C,map_sum,Finset.sum_add_distrib,Finset.smul_sum,Finset.mul_sum]
  simpa only [heq] using h

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem parameterRound2_actual_globalObservedError_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length j : ℕ) (ν : Λ) (e : OpenPartialHomeomorph M D) (r : Fin (m+1)) (coord : Fin N)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (tau ell Cv CP CQ Mphi : ℝ) (hell : 0 < ell) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hCv : 0 ≤ Cv) (hCP : 0 ≤ CP) (hCQ : 0 ≤ CQ) (hMphi : 0 ≤ Mphi)
    (hb : ContDiffOn ℝ ∞ (fun z : X => incrementsGlobalPrimaryB F g input ν (z.1,e.symm z.2)) O)
    (hn : ContDiffOn ℝ ∞ (fun z : X => g.normal ν (z.1,e.symm z.2)) O)
    (hphi : ContDiffOn ℝ ∞ (fun z : X => g.phase ν (z.1,e.symm z.2)) O)
    (hP : ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      parameterRound2_globalCorrection F hF g input length tau true ν β (z.1,e.symm z.2)) O)
    (hQ : ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      parameterRound2_globalCorrection F hF g input length tau false ν β (z.1,e.symm z.2)) O)
    (hVb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => incrementsGlobalPrimaryFree F g input tau ν (y.1,e.symm y.2)) z‖ ≤ Cv*tau)
    (hPb : ∀ k ≤ j+1, ∀ z ∈ S, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun y : X => ∑ β, parameterRound2_globalCorrection F hF g input length tau true ν β
        (y.1,e.symm y.2)) z‖ ≤ CP*tau^2)
    (hQb : ∀ k ≤ j+1, ∀ z ∈ S, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun y : X => ∑ β, parameterRound2_globalCorrection F hF g input length tau false ν β
        (y.1,e.symm y.2)) z‖ ≤ CQ*tau^2)
    (hgrad : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fun x => g.phase ν (y.1,e.symm x)) y.2
        (EuclideanSpace.single r 1)) z‖ ≤ Mphi) :
    let err := fun z : X => incrementsGlobalObservedError F hF g input length tau e z.1 z.2 ν r coord
    ContDiffOn ℝ ∞ err O ∧ ∀ k ≤ j, ∀ z ∈ S,
      ell^k * ‖iteratedFDeriv ℝ k err z‖ ≤
        actualJointPrimaryErrorCost j (EuclideanSpace.single r 1) coord Cv
          (actualJointCorrectionSumCost N 1 coord CP CQ) Mphi * (tau/ell) := by
  intro err
  let b := fun z : X => incrementsGlobalPrimaryB F g input ν (z.1,e.symm z.2)
  let normal := fun z : X => g.normal ν (z.1,e.symm z.2)
  let phi := fun z : X => g.phase ν (z.1,e.symm z.2)
  let P := fun β (z : X) => parameterRound2_globalCorrection F hF g input length tau true ν β (z.1,e.symm z.2)
  let Q := fun β (z : X) => parameterRound2_globalCorrection F hF g input length tau false ν β (z.1,e.symm z.2)
  have hC := parameterRound2_complex_correction_sum_from_vector_sums P Q coord O S hO hSO
    (ContDiffOn.sum (fun β _ => hP β)) (ContDiffOn.sum (fun β _ => hQ β))
    (j+1) ell tau CP CQ hell.le hCP hCQ hPb hQb
  have hCz := actualJointCorrectionSumCost_nonneg 1 coord hCP hCQ
  have hVF : ∀ k ≤ j+1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => (Real.sqrt 2*1*tau*b y) • normal y) z‖ ≤ Cv*tau := by
    simpa only [b,normal,mul_one,incrementsGlobalPrimaryFree] using hVb
  have hout := actual_joint_primary_error_slow_jets b phi normal P Q
    (EuclideanSpace.single r 1) coord O S hO hSO hb hn hphi hP hQ j ell tau Cv
    (actualJointCorrectionSumCost N 1 coord CP CQ) Mphi hell htau htaul hCv hCz hMphi
    hVF hC.2 hgrad
  simpa only [err,b,normal,phi,P,Q,parameterRound2_globalCorrection,
    Bool.false_eq_true,ite_false,ite_true,sub_zero,incrementsGlobalObservedError] using hout

#print axioms parameterRound2_complex_correction_sum_from_vector_sums
#print axioms parameterRound2_actual_globalObservedError_slow_jets
end GlobalEmbedding.Continuation
