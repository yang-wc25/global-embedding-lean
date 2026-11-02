import Probes.ActualPrescribedProbeFirstStep
import Probes.ActualFullProbeConnectionBounds
import Probes.ActualPrimitiveTwoJetBounds

/-!
# Actual prescribed paired Hessian responses with primitive slow errors

The same (8.3) free-plus-original-reconstruction family has the exact required
cosine/sine principal term. The bound below controls the actual native mixed
parameter/Hessian response after subtracting that principal term. All source,
amplitude and unweighted phase bounds are derived from their primitive data.
The fixed connection is explicit; its actual geometric producer is separate.
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

/-- Zero connection recovers the native Hessian exactly. -/
theorem probeFixedConnectionHessian_zero (f : D → V) (x : D) :
    probeFixedConnectionHessian 0 f x = fderiv ℝ (fderiv ℝ f) x := by
  have hz : probeConnectionComposition (0 : D →L[ℝ] D →L[ℝ] D) (fderiv ℝ f x) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp [probeConnectionComposition_apply]
  rw [probeFixedConnectionHessian, hz, sub_zero]

/-- Native cosine and sine Hessian responses, including the true fixed
connection remainder, for the prescribed source itself. -/
theorem actualPrescribedProbe_covariant_hessian_response_bound
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
    (Γ : D →L[ℝ] D →L[ℝ] D) (u : Fin p → ℝ) (x : D) (hx : x ∈ S)
    (i : Fin r) (hw : 0 < weight i) :
    let K := 2 ^ (2 + order + 1) * Bchi i * Bnu i
    let P := Mphase i / weight i
    let Cslow := K / weight i ^ 2 + (2 * P * K + P * K) / weight i
    let Cfirst := K / weight i ^ 2 + P * K / weight i
    let Csum := ∑ l, actualRealHomogeneousConstant m N 2 order Mg
      (homogeneousSourceConstant m N (2 + order + 1) MB
        (probeNormalAmplitudeConstant (2 + order + 1) (weight l) (Bchi l) (Bnu l))) (Mphase l)
    ∀ sine : Bool,
      ‖fderiv ℝ (fun w ↦ probeFixedConnectionHessian Γ
        (actualPrescribedProbeFirstBlock label delta tau weight phase F hF chart chi nu order b w) x) u
        (Pi.single (label (i, sine)) 1) -
        ((delta / tau) * (if sine then Real.sin (weight i * phase i x / tau)
          else Real.cos (weight i * phase i x / tau))) •
          phaseRankOneHessian (phase i) (fun y ↦ chi i (b, y) • (nu i b y : V)) x‖ ≤
        (delta / tau) * ((tau / ell) * (Cslow + (1 + tau * ‖Γ‖) * Csum) +
          tau * Cfirst * ‖Γ‖) := by
  dsimp only
  intro sine
  let q := 2 + order + 1
  let O := (fun x ↦ (b, x)) ⁻¹' Ojoint
  have hO : IsOpen O := hOjoint.preimage (continuous_const.prodMk continuous_id)
  have hsource l := actualPrescribedProbeSource_weighted_jets label l F hF chart (chi l) (nu l)
    Ojoint hOjoint hBrow (hchi l) (hnu l) q ell delta tau (weight l) MB (Bchi l) (Bnu l)
    hell.le hdelta htau.le hMB (hBchi l) (hBnu l) hBrowb (hchib l) (hnub l) b
  have hprofile l := actualProbeProfile_weighted_jets (chi l) (fun z : X ↦ (nu l z.1 z.2 : V))
    Ojoint hOjoint (hchi l) (hnu l) q ell (Bchi l) (Bnu l) hell.le (hBchi l) (hBnu l)
    (hchib l) (hnub l)
  have hslice l := fixed_parameter_slice_weighted_jets
    (fun z : X ↦ chi l z • (nu l z.1 z.2 : V)) Ojoint hOjoint (hprofile l).1 q ell
      (2 ^ q * Bchi l * Bnu l) hell.le (hprofile l).2 b
  let K := 2 ^ q * Bchi i * Bnu i
  let P := Mphase i / weight i
  let Ks (l : Fin r) := homogeneousSourceConstant m N q MB
    (probeNormalAmplitudeConstant q (weight l) (Bchi l) (Bnu l))
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by positivity) (hBchi i)) (hBnu i)
  have hKs l : 0 ≤ Ks l := homogeneousSourceConstant_nonneg m N q hMB
    (probeNormalAmplitudeConstant_nonneg q (weight l) (hBchi l) (hBnu l))
  have hprof := probe_profile_twojet_of_weighted
    (fun y ↦ chi i (b, y) • (nu i b y : V)) x ell K hell
    (fun n hn ↦ (hslice i).2 n (by dsimp [q]; omega) x (hS x hx))
  have hph := probe_phase_twojet_of_weighted (phase i) x
    (((hphaseSmooth i).contDiffAt (hO.mem_nhds (hS x hx))).of_le (by simp))
    ell (weight i) (Mphase i) hell hw (fun n hn ↦ hphase i n hn x hx)
  have hkb (l : Fin r) (a : Fin p) (n : ℕ) (hn : n ≤ 2 + order + 1) (y : D) (hy : y ∈ S) :
      ell ^ n * ‖iteratedFDeriv ℝ n
        (actualPrescribedProbeSource label l F hF chart (chi l) (nu l) delta tau (weight l) b a) y‖ ≤
          Ks l * delta * tau := by
    simpa only [mul_assoc] using (hsource l).2 a n hn y (hS y hy)
  have hbounds := actualFullProbe_connection_remainders_bound label delta tau ell weight phase
    (fun l y ↦ chi l (b, y) • (nu l b y : V)) (F b) (hF b) (chart b) order
    (fun l ↦ actualPrescribedProbeSource label l F hF chart (chi l) (nu l) delta tau (weight l) b)
    O S hO hS hphaseSmooth (fun l ↦ (hslice l).1) hA hB hG hJ hT0
    (fun l a ↦ (hsource l).1 a) Mg Ks Mphase
    hdelta hell hell1 htau htauell hMg hKs hAb hBb hGb hJb hT0b hkb hphase
    x hx i hw K K K P P hK hK hK hph.1 hph.1 hprof.1 hprof.2.1 hprof.2.2 hph.2.1 hph.2.2 Γ
  simp only [actualPrescribedProbeFirstBlock]
  cases sine with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [actualFullProbe_cos_fixed_connection_response label delta tau weight phase
      (fun l y ↦ chi l (b, y) • (nu l b y : V)) (F b) (hF b) (chart b) order
      (fun l ↦ actualPrescribedProbeSource label l F hF chart (chi l) (nu l) delta tau (weight l) b)
      O hO hphaseSmooth (fun l ↦ (hslice l).1) hA hB hG hJ hT0 (fun l a ↦ (hsource l).1 a)
      Γ u x (hS x hx) i htau.ne' hw.ne', add_sub_cancel_left]
    exact hbounds.1
  | true =>
    simp only [↓reduceIte]
    rw [actualFullProbe_sin_fixed_connection_response label delta tau weight phase
      (fun l y ↦ chi l (b, y) • (nu l b y : V)) (F b) (hF b) (chart b) order
      (fun l ↦ actualPrescribedProbeSource label l F hF chart (chi l) (nu l) delta tau (weight l) b)
      O hO hphaseSmooth (fun l ↦ (hslice l).1) hA hB hG hJ hT0 (fun l a ↦ (hsource l).1 a)
      Γ u x (hS x hx) i htau.ne' hw.ne', add_sub_cancel_left]
    exact hbounds.2

/-- The same actual prescribed source has the original sigma*tau/ell
Hessian-response error, uniformly in the probe parameter. -/
theorem actualPrescribedProbe_hessian_response_bound
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
    (u : Fin p → ℝ) (x : D) (hx : x ∈ S)
    (i : Fin r) (hw : 0 < weight i) :
    let K := 2 ^ (2 + order + 1) * Bchi i * Bnu i
    let P := Mphase i / weight i
    let Cslow := K / weight i ^ 2 + (2 * P * K + P * K) / weight i
    let Csum := ∑ l, actualRealHomogeneousConstant m N 2 order Mg
      (homogeneousSourceConstant m N (2 + order + 1) MB
        (probeNormalAmplitudeConstant (2 + order + 1) (weight l) (Bchi l) (Bnu l))) (Mphase l)
    ∀ sine : Bool,
      ‖fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ
        (actualPrescribedProbeFirstBlock label delta tau weight phase F hF chart chi nu order b w)) x) u
        (Pi.single (label (i, sine)) 1) -
        ((delta / tau) * (if sine then Real.sin (weight i * phase i x / tau)
          else Real.cos (weight i * phase i x / tau))) •
          phaseRankOneHessian (phase i) (fun y ↦ chi i (b, y) • (nu i b y : V)) x‖ ≤
        (delta / tau) * (tau / ell) * (Cslow + Csum) := by
  have h := actualPrescribedProbe_covariant_hessian_response_bound label delta tau ell weight phase
    F hF chart chi nu order b Ojoint S hOjoint hS hphaseSmooth hBrow hchi hnu hA hB hG hJ hT0
    MB Mg Bchi Bnu Mphase hdelta hell hell1 htau htauell hMB hMg hBchi hBnu
    hBrowb hchib hnub hAb hBb hGb hJb hT0b hphase 0 u x hx i hw
  simpa only [probeFixedConnectionHessian_zero, norm_zero, mul_zero, add_zero, one_mul,
    mul_assoc] using h

#print axioms actualPrescribedProbe_covariant_hessian_response_bound
#print axioms actualPrescribedProbe_hessian_response_bound
end GlobalEmbedding.Offline
