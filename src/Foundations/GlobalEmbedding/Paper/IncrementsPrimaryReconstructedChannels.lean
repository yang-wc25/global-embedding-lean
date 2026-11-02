import GlobalEmbedding.Paper.IncrementsModeActualReconstruction
import GlobalEmbedding.Paper.IncrementsActualModeSize

/-!
# Actual primary reconstructed correction channels

Source: original lem:increments, main.tex617–661. Only compose the canonical
finite formula, its fixed native real/imaginary channels, and the SAME actual R.
Geometry/source jets remain genuine internal original-data producer obligations.
There is no supplied bound on U, R, P/Q, or the desired primary error.
-/

noncomputable section
open Manifold Filter
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ

/-- Literal correction of a fixed real channel of SAME actual finite u.
Instantiate channel with incrementsModeRealPart or incrementsModeImagPart.
Source: Z=dF(g^-1u)+v_f+JT(u) in original main.tex617–650. -/
def incrementsPrimaryReconstructedChannel (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (channel : Cdata →L[ℝ] D) (tau : ℝ) (p : ℕ) (k : D → Cdata) : D → V :=
  incrementsModeReconstruction F hF c (fun x ↦ channel
    (incrementsActualModeSum (incrementsModeComplexFirstOrderA F hF c)
      (incrementsModeComplexFirstOrderB F hF c) ((tau : ℂ) / Complex.I) p k x))

/-- The actual channel correction is smooth from the genuine source and geometry
fields. No reconstructed-amplitude smoothness is supplied as an input.
Source: original finite differential reconstruction, main.tex638–650. -/
theorem increments_primary_reconstructed_channel_contDiffOn (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (channel : Cdata →L[ℝ] D) (tau : ℝ) (p : ℕ) (k : D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hk : ContDiffOn ℝ ∞ k O) :
    ContDiffOn ℝ ∞ (incrementsPrimaryReconstructedChannel F hF c channel tau p k) O := by
  exact incrementsModeReconstruction_contDiffOn F hF c O hO hG hJ hT0 _
    (channel.contDiff.comp_contDiffOn (increments_actual_mode_sum_contDiffOn _ _ _ p k
      O hO hA hB hk))

/-- Actual reconstructed real/imaginary correction size and SAME source-input
difference. Source jets carry their actual free-amplitude factor tau. The SAME
finite p precedes observation s; at s=j+1 the source budget is j+p+2.
Only tau/ell≤1 is used, never an observation-dependent half-ratio threshold.
Source: original main.tex638–661. -/
theorem increments_primary_reconstructed_channel_scaled_bounds
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (channel : Cdata →L[ℝ] D) (s p : ℕ) (O S : Set D)
    (hO : IsOpen O) (hSO : S ⊆ O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (k kbar : D → Cdata) (hk : ContDiffOn ℝ ∞ k O) (hkbar : ContDiffOn ℝ ∞ kbar O)
    (ell tau Mg K Delta : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (htau : 0 < tau) (htauell : tau ≤ ell) (hMg : 0 ≤ Mg) (hK : 0 ≤ K)
    (hDelta : 0 ≤ Delta)
    (hAb : ∀ i ≤ s + p + 1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderA F hF c) x‖ ≤ Mg)
    (hBb : ∀ i ≤ s + p + 1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderB F hF c) x‖ ≤ Mg)
    (hGb : ∀ i ≤ s, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) x‖ ≤ Mg)
    (hJb : ∀ i ≤ s, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
        (incrementsModeCoordinateJ F hF c y)) x‖ ≤ Mg)
    (hT0b : ∀ i ≤ s, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeTransverseValue F c) x‖ ≤ Mg)
    (hkb : ∀ i ≤ s + p + 1, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i k x‖ ≤ K * tau)
    (hkbarb : ∀ i ≤ s + p + 1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i kbar x‖ ≤ K * tau)
    (hkd : ∀ i ≤ s + p + 1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ k y - kbar y) x‖ ≤ K * tau * Delta) :
    let C := (2 ^ s * Mg + 2 * 2 ^ (s + s) * Mg *
      max Mg ‖incrementsModeTransverseJet (m := m)‖) * ‖channel‖ * K *
        ∑ a ∈ Finset.range p, (2 * 2 ^ (s + p + 1) * Mg) ^ a
    (∀ i ≤ s, ∀ x ∈ S, ell ^ (i + 1) * ‖iteratedFDeriv ℝ i
      (incrementsPrimaryReconstructedChannel F hF c channel tau p k) x‖ ≤ C * tau ^ 2) ∧
    (∀ i ≤ s, ∀ x ∈ S, ell ^ (i + 1) * ‖iteratedFDeriv ℝ i
      (incrementsPrimaryReconstructedChannel F hF c channel tau p kbar) x‖ ≤ C * tau ^ 2) ∧
    (∀ i ≤ s, ∀ x ∈ S, ell ^ (i + 1) * ‖iteratedFDeriv ℝ i
      (fun y ↦ incrementsPrimaryReconstructedChannel F hF c channel tau p k y -
        incrementsPrimaryReconstructedChannel F hF c channel tau p kbar y) x‖ ≤
          C * tau ^ 2 * Delta) := by
  let n := s + p + 1
  let A := incrementsModeComplexFirstOrderA F hF c
  let B := incrementsModeComplexFirstOrderB F hF c
  let alpha := (tau : ℂ) / Complex.I
  let U := incrementsActualModeSum A B alpha p
  let profile := ∑ a ∈ Finset.range p, (2 * 2 ^ n * Mg) ^ a
  let Cr := 2 ^ s * Mg + 2 * 2 ^ (s + s) * Mg *
    max Mg ‖incrementsModeTransverseJet (m := m)‖
  have hprofile : 0 ≤ profile := by dsimp [profile]; positivity
  have hUs (f : D → Cdata) (hf : ContDiffOn ℝ ∞ f O) : ContDiffOn ℝ ∞ (U f) O :=
    increments_actual_mode_sum_contDiffOn A B alpha p f O hO hA hB hf
  have hsum : (∑ a ∈ Finset.range p, ((2 * 2 ^ n * Mg) * tau / ell) ^ a) ≤
      profile := by
    apply Finset.sum_le_sum
    intro a ha
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_iff₀ hell).2
    exact mul_le_mul_of_nonneg_left htauell (by positivity)
  have hUb (f : D → Cdata) (hf : ContDiffOn ℝ ∞ f O) (Kf : ℝ) (hKf : 0 ≤ Kf)
      (hfb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ Kf) :
      ∀ i ≤ s + 1, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i (U f) x‖ ≤
        tau * Kf * profile := by
    intro i hi x hx
    have hh := incrementsModeActualSum_scaled_jet_tau F hF c n p O S hO hSO
      tau htau f hA hB hf ell Mg Kf hell hell1 hMg hKf hAb hBb hfb
      i (by dsimp [n]; omega) x hx
    exact hh.trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg htau.le hKf))
  have hUd : ∀ i ≤ s + 1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ U k y - U kbar y) x‖ ≤
        tau * (K * tau * Delta) * profile := by
    intro i hi x hx
    have he : (fun y ↦ U k y - U kbar y) =ᶠ[𝓝 x] U (fun y ↦ k y - kbar y) := by
      filter_upwards [hO.mem_nhds (hSO hx)] with y hy
      exact (increments_actual_mode_sum_sub A B alpha p k kbar O hO hA hB hk hkbar hy).symm
    rw [(he.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hUb _ (hk.sub hkbar) _ (by positivity) hkd i hi x hx
  have hcs (f : D → Cdata) (hf : ContDiffOn ℝ ∞ f O) :
      ContDiffOn ℝ ∞ (fun y ↦ channel (U f y)) O :=
    channel.contDiff.comp_contDiffOn (hUs f hf)
  have hcb (f : D → Cdata) (hf : ContDiffOn ℝ ∞ f O)
      (hfb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ K * tau) :
      ∀ i ≤ s + 1, ∀ x ∈ S,
        ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ channel (U f y)) x‖ ≤
          ‖channel‖ * (tau * (K * tau) * profile) := by
    intro i hi x hx
    have hh := channel.norm_iteratedFDeriv_comp_left
      ((hUs f hf).contDiffAt (hO.mem_nhds (hSO hx))) (by simp : (i : ℕ∞ω) ≤ ∞)
    calc
      _ ≤ ell ^ i * (‖channel‖ * ‖iteratedFDeriv ℝ i (U f) x‖) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = ‖channel‖ * (ell ^ i * ‖iteratedFDeriv ℝ i (U f) x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hUb f hf _ (by positivity) hfb i hi x hx) (norm_nonneg channel)
  have hcd : ∀ i ≤ s + 1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i
        (fun y ↦ channel (U k y) - channel (U kbar y)) x‖ ≤
          ‖channel‖ * (tau * (K * tau * Delta) * profile) := by
    intro i hi x hx
    have he : (fun y ↦ channel (U k y) - channel (U kbar y)) =
        channel ∘ (fun y ↦ U k y - U kbar y) := funext fun y ↦ (map_sub _ _ _).symm
    rw [he]
    have hh := channel.norm_iteratedFDeriv_comp_left
      (((hUs k hk).sub (hUs kbar hkbar)).contDiffAt (hO.mem_nhds (hSO hx)))
      (by simp : (i : ℕ∞ω) ≤ ∞)
    calc
      _ ≤ ell ^ i * (‖channel‖ * ‖iteratedFDeriv ℝ i (fun y ↦ U k y - U kbar y) x‖) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = ‖channel‖ * (ell ^ i * ‖iteratedFDeriv ℝ i
          (fun y ↦ U k y - U kbar y) x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hUd i hi x hx) (norm_nonneg channel)
  have hr (f : D → Cdata) (hf : ContDiffOn ℝ ∞ f O)
      (hfb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ K * tau) :=
    incrementsModeReconstruction_scaled_jets F hF c s O S hO hSO hG hJ hT0
      (fun y ↦ channel (U f y)) (hcs f hf) ell Mg
      (‖channel‖ * (tau * (K * tau) * profile)) hell hell1 hMg (by positivity)
      hGb hJb hT0b (hcb f hf hfb)
  have hrd := incrementsModeReconstruction_difference_scaled_jets F hF c s O S hO hSO
    hG hJ hT0 (fun y ↦ channel (U k y)) (fun y ↦ channel (U kbar y))
    (hcs k hk) (hcs kbar hkbar) ell Mg
    (‖channel‖ * (tau * (K * tau * Delta) * profile)) hell hell1 hMg (by positivity)
    hGb hJb hT0b hcd
  refine ⟨?_, ?_, ?_⟩
  · intro i hi x hx
    convert hr k hk hkb i hi x hx using 1 <;>
      dsimp [incrementsPrimaryReconstructedChannel, U, A, B, alpha, profile, n]; ring
  · intro i hi x hx
    convert hr kbar hkbar hkbarb i hi x hx using 1 <;>
      dsimp [incrementsPrimaryReconstructedChannel, U, A, B, alpha, profile, n]; ring
  · intro i hi x hx
    convert hrd i hi x hx using 1 <;>
      dsimp [incrementsPrimaryReconstructedChannel, U, A, B, alpha, profile, n]; ring

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.incrementsPrimaryReconstructedChannel
#print axioms GlobalEmbedding.Paper.increments_primary_reconstructed_channel_contDiffOn
#print axioms GlobalEmbedding.Paper.increments_primary_reconstructed_channel_scaled_bounds
