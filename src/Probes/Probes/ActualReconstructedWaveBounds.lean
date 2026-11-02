import Probes.ActualReconstructedOscillation

/-!
# Quantitative slow remainder of the actual oscillating homogeneous correction

The actual source has size delta*tau. The ORIGINAL finite solver and ORIGINAL
Gram/normal reconstruction give an amplitude of size delta*tau²/ell. The same
actual sine/cosine multiplier then gives the C² remainder delta/ell, equivalently
(delta/tau)*(tau/ell). This is the slow relative factor required in (8.3).
All coefficient hypotheses below concern the actual original geometry fields
and source jets. No bound on the desired correction or its parameter response
is assumed. The finite iteration length p is the same at every observation order.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Filter Set
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation

/-- Exact original reconstruction constant, with delta factored out of the
actual source bound. Only dimension, fixed channel, orders and geometric/input
jet bounds occur. -/
def reconstructedChannelConstant (m s p : ℕ) (Mg K channelNorm : ℝ) : ℝ :=
  (2 ^ s * Mg + 2 * 2 ^ (s+s) * Mg * max Mg ‖incrementsModeTransverseJet (m := m)‖) *
    channelNorm * K * ∑ a ∈ Finset.range p, (2 * 2 ^ (s+p+1) * Mg) ^ a

theorem reconstructedChannelConstant_nonneg (m s p : ℕ) {Mg K C : ℝ}
    (hMg : 0 ≤ Mg) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    0 ≤ reconstructedChannelConstant m s p Mg K C := by
  unfold reconstructedChannelConstant
  positivity

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m+1) → ℂ

/-- All actual fast spatial jets of the actual homogeneous correction retain
the extra slow factor tau/ell relative to the free probe amplitude delta*tau.
The constant precedes the observation point and derivative order. -/
theorem actualReconstructedWave_weighted_bounds
    (sine : Bool) (phi : D → ℝ) (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (channel : Cdata →L[ℝ] D) (s p : ℕ) (O S : Set D)
    (hO : IsOpen O) (hSO : S ⊆ O)
    (hphi : ContDiffOn ℝ ∞ phi O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y => freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y => (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (k : D → Cdata) (hk : ContDiffOn ℝ ∞ k O)
    (delta ell tau Mg K Mphase : ℝ)
    (hdelta : 0 ≤ delta) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hMg : 0 ≤ Mg) (hK : 0 ≤ K)
    (hAb : ∀ i ≤ s+p+1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderA F hF c) x‖ ≤ Mg)
    (hBb : ∀ i ≤ s+p+1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderB F hF c) x‖ ≤ Mg)
    (hGb : ∀ i ≤ s, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y => freeGramRightInverse (fderiv ℝ (F ∘ c) y)) x‖ ≤ Mg)
    (hJb : ∀ i ≤ s, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y => (normalSpace (I := I) F (c y)).subtypeL.comp
        (incrementsModeCoordinateJ F hF c y)) x‖ ≤ Mg)
    (hT0b : ∀ i ≤ s, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeTransverseValue F c) x‖ ≤ Mg)
    (hkb : ∀ i ≤ s+p+1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i k x‖ ≤ K * delta * tau)
    (hphase : ∀ i < s, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ (i+1) phi x‖ ≤ Mphase) :
    let C := euclideanTargetCoordinateCost N * incrementsFastMultiplierConstant s Mphase *
      reconstructedChannelConstant m s p Mg K ‖channel‖
    ∀ n ≤ s, ∀ x ∈ S,
      tau ^ n * ‖iteratedFDeriv ℝ n (actualReconstructedWave sine phi F hF c channel tau p k) x‖ ≤
        C * delta * tau ^ 2 / ell := by
  dsimp only
  let Cr := reconstructedChannelConstant m s p Mg K ‖channel‖
  have hCr : 0 ≤ Cr := reconstructedChannelConstant_nonneg m s p hMg hK (norm_nonneg _)
  have hdiff : ∀ i ≤ s+p+1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun y => k y - k y) x‖ ≤ (K * delta) * tau * 0 := by
    intro i hi x hx
    simp
  have hbase := (increments_primary_reconstructed_channel_scaled_bounds F hF c channel s p O S hO hSO
    hA hB hG hJ hT0 k k hk hk ell tau Mg (K*delta) 0 hell hell1 htau htaul hMg
    (mul_nonneg hK hdelta) le_rfl hAb hBb hGb hJb hT0b hkb hkb hdiff).1
  have hRs := increments_primary_reconstructed_channel_contDiffOn F hF c channel tau p k
    O hO hA hB hG hJ hT0 hk
  have hRbound : ∀ i ≤ s, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (incrementsPrimaryReconstructedChannel F hF c channel tau p k) x‖ ≤
        Cr * delta * tau ^ 2 / ell := by
    intro i hi x hx
    apply (le_div_iff₀ hell).mpr
    have hb := hbase i hi x hx
    convert hb using 1 <;> simp only [Cr, reconstructedChannelConstant, pow_succ] <;> ring
  intro n hn x hx
  have h := actualTrigModulation_weighted_jet_bound sine s n hn O hO phi
    (incrementsPrimaryReconstructedChannel F hF c channel tau p k) hphi hRs x (hSO hx)
    tau ell Mphase (Cr * delta * tau ^ 2 / ell) htau htaul hell1
    (by positivity) (fun i hi => hphase i hi x hx) (fun i hi => hRbound i hi x hx)
  apply h.trans_eq
  dsimp only [actualReconstructedWave, Cr]
  ring

section Scales
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The weighted true-wave bound gives its actual value, first derivative and
Hessian scales. In applications h is supplied by the theorem above, including
for the native parameter columns by their proved germ identity. -/
theorem actual_wave_value_first_second_scales (W : X → Y) (x : X)
    (C delta tau ell : ℝ) (htau : 0 < tau)
    (h : ∀ n ≤ 2, tau ^ n * ‖iteratedFDeriv ℝ n W x‖ ≤ C * delta * tau ^ 2 / ell) :
    ‖W x‖ ≤ C * (delta * tau) * (tau / ell) ∧
    ‖fderiv ℝ W x‖ ≤ C * delta * (tau / ell) ∧
    ‖fderiv ℝ (fderiv ℝ W) x‖ ≤ C * (delta / tau) * (tau / ell) := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 le_rfl
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h0
  simp only [pow_one, norm_iteratedFDeriv_one] at h1
  have he : ‖iteratedFDeriv ℝ 2 W x‖ = ‖fderiv ℝ (fderiv ℝ W) x‖ := by
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
  rw [he] at h2
  refine ⟨h0.trans_eq (by ring), ?_, ?_⟩
  · apply (mul_le_mul_iff_right₀ htau).mp
    apply h1.trans_eq
    ring
  · apply (mul_le_mul_iff_right₀ (pow_pos htau 2)).mp
    apply h2.trans_eq
    field_simp

end Scales

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualReconstructedWave_weighted_bounds
#print axioms GlobalEmbedding.Continuation.actual_wave_value_first_second_scales
