import Probes.ActualPrescribedProbeFirstStep
import Probes.ActualFullProbeValue

/-!
# Actual prescribed paired value responses with primitive slow errors

The same (8.3) free-plus-original-reconstruction family has its original
negative cosine/sine value principal term. The actual parameter derivative
minus that term is bounded by a*(tau/ell)*Csum, with the exact same finite
source constants used by the Hessian estimate. Primitive true-B, chi and nu
profiles produce every source budget.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Manifold Set
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Offline

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

private noncomputable local instance prescribedBilinearSemi :
    SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance prescribedBilinearNormed :
    NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance prescribedBilinearSpace :
    NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := ContinuousLinearMap.toNormedSpace

theorem actualPrescribedProbe_value_response_bound
    (label : (Fin r × Bool) ↪ Fin p) (delta tau ell : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ, V) ∞ (F b))
    (chart : Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (chart b x))
    (order : ℕ) (b : Ep) (Ojoint : Set X) (S : Set D)
    (hOjoint : IsOpen Ojoint) (hS : ∀ x ∈ S, (b, x) ∈ Ojoint)
    (hphaseSmooth : ∀ l, ContDiffOn ℝ ∞ (phase l) ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hBrow : ContDiffOn ℝ ∞ (fun z : X ↦ fun i : Fin (m + 1) ↦
      (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 i : V)) Ojoint)
    (hchi : ∀ l, ContDiffOn ℝ ∞ (chi l) Ojoint)
    (hnu : ∀ l, ContDiffOn ℝ ∞ (fun z : X ↦ (nu l z.1 z.2 : V)) Ojoint)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA (F b) (hF b) (chart b))
      ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB (F b) (hF b) (chart b))
      ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F b ∘ chart b) y))
      ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) (F b) (chart b y)).subtypeL.comp
      (incrementsModeCoordinateJ (F b) (hF b) (chart b) y)) ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue (F b) (chart b))
      ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (MB Mg : ℝ) (Bchi Bnu Mphase : Fin r → ℝ)
    (hdelta : 0 ≤ delta) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (htau : 0 < tau) (htauell : tau ≤ ell) (hMB : 0 ≤ MB) (hMg : 0 ≤ Mg)
    (hBchi : ∀ l, 0 ≤ Bchi l) (hBnu : ∀ l, 0 ≤ Bnu l)
    (hBrowb : ∀ a ≤ 2 + order + 1, ∀ z ∈ Ojoint, ell ^ a * ‖iteratedFDeriv ℝ a
      (fun y : X ↦ fun i : Fin (m + 1) ↦
        (incrementsModeSecondForm (F y.1) (hF y.1) (chart y.1) y.2 0 i : V)) z‖ ≤ MB)
    (hchib : ∀ l a, a ≤ 2 + order + 1 → ∀ z ∈ Ojoint,
      ell ^ a * ‖iteratedFDeriv ℝ a (chi l) z‖ ≤ Bchi l)
    (hnub : ∀ l a, a ≤ 2 + order + 1 → ∀ z ∈ Ojoint,
      ell ^ a * ‖iteratedFDeriv ℝ a (fun y : X ↦ (nu l y.1 y.2 : V)) z‖ ≤ Bnu l)
    (hAb : ∀ a ≤ 2 + order + 1, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (incrementsModeComplexFirstOrderA (F b) (hF b) (chart b)) y‖ ≤ Mg)
    (hBb : ∀ a ≤ 2 + order + 1, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (incrementsModeComplexFirstOrderB (F b) (hF b) (chart b)) y‖ ≤ Mg)
    (hGb : ∀ a ≤ 2, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (fun z ↦ freeGramRightInverse (fderiv ℝ (F b ∘ chart b) z)) y‖ ≤ Mg)
    (hJb : ∀ a ≤ 2, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (fun z ↦ (normalSpace (I := I) (F b) (chart b z)).subtypeL.comp
        (incrementsModeCoordinateJ (F b) (hF b) (chart b) z)) y‖ ≤ Mg)
    (hT0b : ∀ a ≤ 2, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (incrementsModeTransverseValue (F b) (chart b)) y‖ ≤ Mg)
    (hphase : ∀ l a, a < 2 → ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ (a + 1) (fun z ↦ weight l * phase l z) y‖ ≤ Mphase l)
    (u : Fin p → ℝ) (x : D) (hx : x ∈ S) (i : Fin r) :
    let Csum := ∑ l, actualRealHomogeneousConstant m N 2 order Mg
      (homogeneousSourceConstant m N (2 + order + 1) MB
        (probeNormalAmplitudeConstant (2 + order + 1) (weight l) (Bchi l) (Bnu l))) (Mphase l)
    ∀ sine : Bool,
      ‖fderiv ℝ (fun w ↦ actualPrescribedProbeFirstBlock label delta tau weight phase
        F hF chart chi nu order b w x) u (Pi.single (label (i, sine)) 1) -
        (if sine then actualProbeSinColumn delta tau (weight i) (phase i)
          (fun y ↦ chi i (b, y) • (nu i b y : V)) x
        else actualProbeCosColumn delta tau (weight i) (phase i)
          (fun y ↦ chi i (b, y) • (nu i b y : V)) x)‖ ≤
        (delta * tau) * (tau / ell) * Csum := by
  dsimp only
  intro sine
  let q := 2 + order + 1
  let O := (fun x ↦ (b, x)) ⁻¹' Ojoint
  have hO : IsOpen O := hOjoint.preimage (continuous_const.prodMk continuous_id)
  have hsource l := actualPrescribedProbeSource_weighted_jets label l F hF chart (chi l) (nu l)
    Ojoint hOjoint hBrow (hchi l) (hnu l) q ell delta tau (weight l) MB (Bchi l) (Bnu l)
    hell.le hdelta htau.le hMB (hBchi l) (hBnu l) hBrowb (hchib l) (hnub l) b
  let Ks (l : Fin r) := homogeneousSourceConstant m N q MB
    (probeNormalAmplitudeConstant q (weight l) (Bchi l) (Bnu l))
  let Cr (l : Fin r) := actualRealHomogeneousConstant m N 2 order Mg (Ks l) (Mphase l)
  have hKs l : 0 ≤ Ks l := homogeneousSourceConstant_nonneg m N q hMB
    (probeNormalAmplitudeConstant_nonneg q (weight l) (hBchi l) (hBnu l))
  have hkb (l : Fin r) (a : Fin p) (n : ℕ) (hn : n ≤ 2 + order + 1) (y : D) (hy : y ∈ S) :
      ell ^ n * ‖iteratedFDeriv ℝ n
        (actualPrescribedProbeSource label l F hF chart (chi l) (nu l) delta tau (weight l) b a) y‖ ≤
          Ks l * delta * tau := by
    simpa only [mul_assoc] using (hsource l).2 a n hn y (hS y hy)
  have hrec (l : Fin r) := actualRealHomogeneousProbe_weighted_bounds (fun y ↦ weight l * phase l y)
    (F b) (hF b) (chart b) 2 order O S hO hS ((hphaseSmooth l).const_smul (weight l))
    hA hB hG hJ hT0
    (actualPrescribedProbeSource label l F hF chart (chi l) (nu l) delta tau (weight l) b (label (i, sine)))
    ((hsource l).1 (label (i, sine))) delta ell tau Mg (Ks l) (Mphase l)
    hdelta hell hell1 htau htauell hMg (hKs l) hAb hBb hGb hJb hT0b
    (hkb l (label (i, sine))) (hphase l)
  have hv (l : Fin r) :
      ‖actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) (F b) (hF b) (chart b) tau order
        (actualPrescribedProbeSource label l F hF chart (chi l) (nu l) delta tau (weight l) b (label (i, sine))) x‖ ≤
          Cr l * (delta * tau) * (tau / ell) :=
    (actual_wave_value_first_second_scales _ x (Cr l) delta tau ell htau
      (fun n hn ↦ hrec l n hn x hx)).1
  simp only [actualPrescribedProbeFirstBlock]
  rw [actualFullProbe_value_response_sub_principal label delta tau weight phase
    (fun l y ↦ chi l (b, y) • (nu l b y : V)) (F b) (hF b) (chart b) order
    (fun l ↦ actualPrescribedProbeSource label l F hF chart (chi l) (nu l) delta tau (weight l) b)
    O hO hA hB (fun l a ↦ (hsource l).1 a) u x (hS x hx) i sine]
  calc
    _ ≤ ∑ l, ‖actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) (F b) (hF b) (chart b) tau order
        (actualPrescribedProbeSource label l F hF chart (chi l) (nu l) delta tau (weight l) b (label (i, sine))) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ l, Cr l * (delta * tau) * (tau / ell) := Finset.sum_le_sum (fun l _ ↦ hv l)
    _ = _ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring

#print axioms actualPrescribedProbe_value_response_bound
end GlobalEmbedding.Offline
