import Probes.ActualRealHomogeneousProbe

/-!
# Original slow bounds for the actual real homogeneous correction

Both real and imaginary reconstruction channels are accounted for in one
explicit constant. The estimates are produced from actual geometry and source
jets by the original finite solver, with the SAME finite truncation p at every
observation order. The source is not replaced by an assumed correction bound.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Manifold Set
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Offline

/-- The finite constant includes both original reconstructed channels and the
actual Euclidean/Pi operator norm costs. -/
def actualRealHomogeneousConstant (m N s p : ℕ) (Mg K Mphase : ℝ) : ℝ :=
  euclideanTargetCoordinateCost N * incrementsFastMultiplierConstant s Mphase *
    (reconstructedChannelConstant m s p Mg K ‖incrementsModeRealPart (m := m)‖ +
      reconstructedChannelConstant m s p Mg K ‖incrementsModeImagPart (m := m)‖)

theorem actualRealHomogeneousConstant_nonneg (m N s p : ℕ) (Mg K Mphase : ℝ)
    (hMg : 0 ≤ Mg) (hK : 0 ≤ K) : 0 ≤ actualRealHomogeneousConstant m N s p Mg K Mphase :=
  mul_nonneg (mul_nonneg (euclideanTargetCoordinateCost_nonneg N)
    (incrementsFastMultiplierConstant_pos s Mphase).le)
    (add_nonneg (reconstructedChannelConstant_nonneg m s p hMg hK (norm_nonneg _))
      (reconstructedChannelConstant_nonneg m s p hMg hK (norm_nonneg _)))

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ

/-- All spatial jets of the ACTUAL real homogeneous correction have the
required extra tau/ell gain. Every bound concerns primitive native geometry
and source jets, with a scale-independent constant. -/
theorem actualRealHomogeneousProbe_weighted_bounds
    (phi : D → ℝ) (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (s p : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (hphi : ContDiffOn ℝ ∞ phi O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (k : D → Cdata) (hk : ContDiffOn ℝ ∞ k O)
    (δ ell τ Mg K Mphase : ℝ)
    (hδ : 0 ≤ δ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hτ : 0 < τ) (hτell : τ ≤ ell) (hMg : 0 ≤ Mg) (hK : 0 ≤ K)
    (hAb : ∀ i ≤ s+p+1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderA F hF c) x‖ ≤ Mg)
    (hBb : ∀ i ≤ s+p+1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderB F hF c) x‖ ≤ Mg)
    (hGb : ∀ i ≤ s, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) x‖ ≤ Mg)
    (hJb : ∀ i ≤ s, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
        (incrementsModeCoordinateJ F hF c y)) x‖ ≤ Mg)
    (hT0b : ∀ i ≤ s, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeTransverseValue F c) x‖ ≤ Mg)
    (hkb : ∀ i ≤ s+p+1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i k x‖ ≤ K * δ * τ)
    (hphase : ∀ i < s, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ (i+1) phi x‖ ≤ Mphase) :
    ∀ n ≤ s, ∀ x ∈ S,
      τ ^ n * ‖iteratedFDeriv ℝ n (actualRealHomogeneousProbe phi F hF c τ p k) x‖ ≤
        actualRealHomogeneousConstant m N s p Mg K Mphase * δ * τ ^ 2 / ell := by
  have hr := actualReconstructedWave_weighted_bounds false phi F hF c incrementsModeRealPart
    s p O S hO hSO hphi hA hB hG hJ hT0 k hk δ ell τ Mg K Mphase
    hδ hell hell1 hτ hτell hMg hK hAb hBb hGb hJb hT0b hkb hphase
  have hi := actualReconstructedWave_weighted_bounds true phi F hF c incrementsModeImagPart
    s p O S hO hSO hphi hA hB hG hJ hT0 k hk δ ell τ Mg K Mphase
    hδ hell hell1 hτ hτell hMg hK hAb hBb hGb hJb hT0b hkb hphase
  have hRs := actualTrigModulation_contDiffOn false phi τ _ O hphi
    (increments_primary_reconstructed_channel_contDiffOn F hF c incrementsModeRealPart
      τ p k O hO hA hB hG hJ hT0 hk)
  have hIs := actualTrigModulation_contDiffOn true phi τ _ O hphi
    (increments_primary_reconstructed_channel_contDiffOn F hF c incrementsModeImagPart
      τ p k O hO hA hB hG hJ hT0 hk)
  intro n hn x hx
  have hRn : ContDiffAt ℝ n
      (actualReconstructedWave false phi F hF c incrementsModeRealPart τ p k) x :=
    (hRs.contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp)
  have hIn : ContDiffAt ℝ n
      (actualReconstructedWave true phi F hF c incrementsModeImagPart τ p k) x :=
    (hIs.contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp)
  change τ ^ n * ‖iteratedFDeriv ℝ n (fun y ↦
    actualReconstructedWave false phi F hF c incrementsModeRealPart τ p k y -
    actualReconstructedWave true phi F hF c incrementsModeImagPart τ p k y) x‖ ≤ _
  rw [fun_iteratedFDeriv_sub_apply hRn hIn]
  calc
    _ ≤ τ ^ n * (‖iteratedFDeriv ℝ n
        (actualReconstructedWave false phi F hF c incrementsModeRealPart τ p k) x‖ +
      ‖iteratedFDeriv ℝ n
        (actualReconstructedWave true phi F hF c incrementsModeImagPart τ p k) x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (pow_nonneg hτ.le n)
    _ = τ ^ n * ‖iteratedFDeriv ℝ n
        (actualReconstructedWave false phi F hF c incrementsModeRealPart τ p k) x‖ +
      τ ^ n * ‖iteratedFDeriv ℝ n
        (actualReconstructedWave true phi F hF c incrementsModeImagPart τ p k) x‖ := by ring
    _ ≤ _ := add_le_add (hr n hn x hx) (hi n hn x hx)
    _ = _ := by unfold actualRealHomogeneousConstant; ring

#print axioms actualRealHomogeneousProbe_weighted_bounds
end GlobalEmbedding.Offline
