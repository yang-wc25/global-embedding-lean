import Probes.ActualSecondaryConstructedCancellation

/-!
# The actual observation chart returns the original localized forcing

The transition here is the genuine composition of the observation inverse
and the constructed adapted chart. The local hR/hI are bound to the actual
inverse-Jacobian localization of the original negative quadratic tensor.
The ordinary subordinate partition therefore recovers the original forcing
in the observation chart, including every ordered nonzero signed record.
-/

noncomputable section
open Manifold Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep M Label Sub : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

variable {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}

theorem actual_observed_secondary_forcing_eq_returned
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (d : ActualSecondaryPieceData (I := 𝓙) (m := m) F hF n j ell Mg CH delta W)
    (b : OpenPartialHomeomorph (Ep × M) X)
    (cutoff : X → ℝ) (HR HI : X → Tensor)
    (hR : EqOn d.hR (actualSecondaryInverseForcing (b.symm.trans d.chart) cutoff HR)
      (b.symm.trans d.chart).target)
    (hI : EqOn d.hI (actualSecondaryInverseForcing (b.symm.trans d.chart) cutoff HI)
      (b.symm.trans d.chart).target)
    (tau : ℝ) (z : X) (hz : z ∈ b.target) :
    actualObservedSecondaryForcingTensor F hF d b.symm tau z =
      actualSecondaryReturnedForcing (b.symm.trans d.chart) cutoff HR HI tau z := by
  have hsource : z ∈ (b.symm.trans d.chart).source ↔ b.symm z ∈ d.chart.source := by
    rw [OpenPartialHomeomorph.trans_source]
    change (z ∈ b.target ∧ b.symm z ∈ d.chart.source) ↔ _
    exact and_iff_right hz
  unfold actualObservedSecondaryForcingTensor actualSecondaryReturnedForcing
  rw [hsource]
  split_ifs with hs
  · have hzs : z ∈ (b.symm.trans d.chart).source := hsource.mpr hs
    have hrt := hR ((b.symm.trans d.chart).map_source hzs)
    have hit := hI ((b.symm.trans d.chart).map_source hzs)
    change d.hR (d.chart (b.symm z)) = _ at hrt
    change d.hI (d.chart (b.symm z)) = _ at hit
    simp only [actualSecondaryLocalForcingTensor,hrt,hit]
    rfl
  · rfl

/-- Only the support of the actual localized forcing must lie in the chart.
The ordinary scalar cutoff may extend across the boundary of the primary pair. -/
theorem actual_secondary_returned_forcing_eq_at_active
    (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ ∞ e e.source) (hinv : ContDiffOn ℝ ∞ e.symm e.target)
    (hfirst : ∀ y ∈ e.source, (e y).1 = y.1)
    (HR HI : X → Tensor) (cutoff phase : X → ℝ)
    (hadapted : ∀ y ∈ e.source, (e y).2 0 = phase y)
    (tau : ℝ) (z : X)
    (hsupport : cutoff z ≠ 0 → HR z ≠ 0 ∨ HI z ≠ 0 → z ∈ e.source) :
    actualSecondaryReturnedForcing e cutoff HR HI tau z =
      cutoff z • (Real.cos (phase z / tau) • HR z - Real.sin (phase z / tau) • HI z) := by
  unfold actualSecondaryReturnedForcing
  split_ifs with hz
  · exact actual_secondary_forcing_pullback_cancel e he hinv hfirst HR HI cutoff phase hadapted tau z hz
  · by_cases h : HR z ≠ 0 ∨ HI z ≠ 0
    · have hcutoff : cutoff z = 0 := not_not.mp (fun hn => hz (hsupport hn h))
      rw [hcutoff]
      ext v w
      simp only [smul_apply, smul_eq_mul, zero_apply, zero_mul]
    · have hR : HR z = 0 := not_not.mp (not_or.mp h).1
      have hI : HI z = 0 := not_not.mp (not_or.mp h).2
      rw [hR, hI]
      ext v w
      simp only [smul_apply, sub_apply, smul_eq_mul, zero_apply, mul_zero, sub_self]

theorem actual_secondary_forcing_partition_sum_at_active
    {Sub : Type*} [Fintype Sub]
    (e : Sub → OpenPartialHomeomorph X X)
    (he : ∀ a, ContDiffOn ℝ ∞ (e a) (e a).source)
    (hinv : ∀ a, ContDiffOn ℝ ∞ (e a).symm (e a).target)
    (hfirst : ∀ a y, y ∈ (e a).source → ((e a) y).1 = y.1)
    (HR HI : X → Tensor) (cutoff : Sub → X → ℝ) (phase : X → ℝ)
    (hadapted : ∀ a y, y ∈ (e a).source → ((e a) y).2 0 = phase y)
    (tau : ℝ) (z : X)
    (hsupport : ∀ a, cutoff a z ≠ 0 → HR z ≠ 0 ∨ HI z ≠ 0 → z ∈ (e a).source)
    (hpartition : HR z ≠ 0 ∨ HI z ≠ 0 → ∑ a, cutoff a z = 1) :
    (∑ a, actualSecondaryReturnedForcing (e a) (cutoff a) HR HI tau z) =
      Real.cos (phase z / tau) • HR z - Real.sin (phase z / tau) • HI z := by
  simp_rw [actual_secondary_returned_forcing_eq_at_active (e _) (he _) (hinv _) (hfirst _) HR HI
    (cutoff _) phase (hadapted _) tau z (hsupport _)]
  rw [← Finset.sum_smul]
  by_cases h : HR z ≠ 0 ∨ HI z ≠ 0
  · rw [hpartition h, one_smul]
  · have hR : HR z = 0 := not_not.mp (not_or.mp h).1
    have hI : HI z = 0 := not_not.mp (not_or.mp h).2
    rw [hR, hI]
    ext v w
    simp only [smul_apply, sub_apply, smul_eq_mul, zero_apply, mul_zero, sub_self]

/-- A concrete localization choice for a single original quadratic record.
All fields refer to the actual chart and actual forcing formula. -/
structure ActualSecondaryForcingBinding
    [Fintype Sub]
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (d : Sub → ActualSecondaryPieceData (I := 𝓙) (m := m) F hF n j ell Mg CH delta W)
    (b : OpenPartialHomeomorph (Ep × M) X)
    (HR HI : X → Tensor) (phase : X → ℝ) : Type _ where
  cutoff : Sub → X → ℝ
  transition : ∀ a, ContDiffOn ℝ ∞ (b.symm.trans (d a).chart) (b.symm.trans (d a).chart).source
  inverseTransition : ∀ a, ContDiffOn ℝ ∞ (b.symm.trans (d a).chart).symm
    (b.symm.trans (d a).chart).target
  first : ∀ a y, y ∈ (b.symm.trans (d a).chart).source →
    ((b.symm.trans (d a).chart) y).1 = y.1
  cutoffSupport : ∀ a z, z ∈ b.target → b.symm z ∈ W → cutoff a z ≠ 0 → HR z ≠ 0 ∨ HI z ≠ 0 →
    z ∈ (b.symm.trans (d a).chart).source
  adaptation : ∀ a y, y ∈ (b.symm.trans (d a).chart).source →
    ((b.symm.trans (d a).chart) y).2 0 = phase y
  realForcing : ∀ a, EqOn (d a).hR
    (actualSecondaryInverseForcing (b.symm.trans (d a).chart) (cutoff a) HR)
    (b.symm.trans (d a).chart).target
  imagForcing : ∀ a, EqOn (d a).hI
    (actualSecondaryInverseForcing (b.symm.trans (d a).chart) (cutoff a) HI)
    (b.symm.trans (d a).chart).target
  partition : ∀ z ∈ b.target, b.symm z ∈ W → HR z ≠ 0 ∨ HI z ≠ 0 → ∑ a, cutoff a z = 1

theorem actual_secondary_observed_forcing_partition
    [Fintype Sub]
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (d : Sub → ActualSecondaryPieceData (I := 𝓙) (m := m) F hF n j ell Mg CH delta W)
    (b : OpenPartialHomeomorph (Ep × M) X)
    (HR HI : X → Tensor) (phase : X → ℝ)
    (binding : ActualSecondaryForcingBinding F hF d b HR HI phase)
    (tau : ℝ) (z : X) (hz : z ∈ b.target) (hzW : b.symm z ∈ W) :
    (∑ a, actualObservedSecondaryForcingTensor F hF (d a) b.symm tau z) =
      Real.cos (phase z / tau) • HR z - Real.sin (phase z / tau) • HI z := by
  have heq : ∀ a, actualObservedSecondaryForcingTensor F hF (d a) b.symm tau z =
      actualSecondaryReturnedForcing (b.symm.trans (d a).chart) (binding.cutoff a) HR HI tau z :=
    fun a => actual_observed_secondary_forcing_eq_returned F hF (d a) b (binding.cutoff a)
      HR HI (binding.realForcing a) (binding.imagForcing a) tau z hz
  simp_rw [heq]
  exact actual_secondary_forcing_partition_sum_at_active (fun a => b.symm.trans (d a).chart)
    binding.transition binding.inverseTransition binding.first HR HI binding.cutoff phase
    binding.adaptation tau z (fun a => binding.cutoffSupport a z hz hzW) (binding.partition z hz hzW)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_returned_forcing_eq_at_active
#print axioms GlobalEmbedding.Continuation.actual_secondary_forcing_partition_sum_at_active
#print axioms GlobalEmbedding.Continuation.actual_observed_secondary_forcing_eq_returned
#print axioms GlobalEmbedding.Continuation.actual_secondary_observed_forcing_partition
