import Probes.ActualSecondaryLocalizedForcingSupport
import Smoothing.ParameterRound2GlobalCorrectionSupport

/-! The literal inverse-chart quadratic forcing only needs support of the
actual cutoff restricted to the true open parameter germ. This permits
supports meeting the germ boundary without adding a new cutoff or changing
the finite source. -/

noncomputable section
open Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m : ℕ} {Ep P0 : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace P0]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

theorem actual_secondary_host_cutoff_relative_support
    (b : OpenPartialHomeomorph P0 X) (cutoff : P0 → ℝ)
    (W K : Set P0) (hW : IsOpen W)
    (hsupport : tsupport (fun y : W => cutoff y.val) ⊆ Subtype.val ⁻¹' K)
    (y : X) (hy : y ∈ b.target) (hyW : b.symm y ∈ W)
    (hs : y ∈ tsupport (cutoff ∘ b.symm)) : b.symm y ∈ K := by
  by_contra hn
  have hz := parameterRound2_relative_observation_zero_germ cutoff W K hW hsupport
    b.symm y (b.symm.continuousOn.continuousAt (b.open_target.mem_nhds hy)) hyW hn
  exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hs

theorem actual_secondary_inverse_forcing_relative_support
    (a b : OpenPartialHomeomorph P0 X) (hhost : a.source ⊆ b.source)
    (cutoff : P0 → ℝ) (HR HI : X → Tensor)
    (W K : Set P0) (hW : IsOpen W) (hsource : a.source ⊆ W)
    (hsupport : tsupport (fun y : W => cutoff y.val) ⊆ Subtype.val ⁻¹' K) :
    let t := b.symm.trans a
    let hR := actualSecondaryInverseForcing t (cutoff ∘ b.symm) HR
    let hI := actualSecondaryInverseForcing t (cutoff ∘ b.symm) HI
    ∀ z ∈ a.target, z ∈ tsupport hR ∪ tsupport hI → a.symm z ∈ K := by
  intro t hR hI z hz hzs
  have hzt : z ∈ t.target := ⟨hz,hhost (a.map_target hz)⟩
  have hy : t.symm z ∈ b.target := (t.map_target hzt).1
  have heq : b.symm (t.symm z) = a.symm z := b.left_inv (hhost (a.map_target hz))
  have hyW : b.symm (t.symm z) ∈ W := by
    rw [heq]
    exact hsource (a.map_target hz)
  have hs : t.symm z ∈ tsupport (cutoff ∘ b.symm) := by
    rcases hzs with h | h
    · exact (actual_secondary_inverse_forcing_support t (cutoff ∘ b.symm) HR z hzt h).1
    · exact (actual_secondary_inverse_forcing_support t (cutoff ∘ b.symm) HI z hzt h).1
  have hout := actual_secondary_host_cutoff_relative_support b cutoff W K hW hsupport
    (t.symm z) hy hyW hs
  rwa [heq] at hout

#print axioms actual_secondary_host_cutoff_relative_support
#print axioms actual_secondary_inverse_forcing_relative_support
end GlobalEmbedding.Continuation
