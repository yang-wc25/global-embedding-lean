import Probes.ActualSecondaryForcingPullback
import Probes.ActualSecondaryFiniteTensorIdentity

/-!
# Exact ordinary-partition cancellation of the original negative forcing

The cutoffs form an ordinary partition on actual forcing activity. Each
localized forcing uses a genuine inverse transition and is returned by its
actual forward Jacobian. The sum is exactly the SAME nonzero quadratic
forcing of the SAME primary sine/cosine expansion. There is no square
partition, averaging operation or changed phase list.
-/

noncomputable section
open Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
local notation "CMatrix" => Fin (m+1) → Fin (m+1) → ℂ

def actualImaginaryTensorAssembly (H : CMatrix) : Tensor :=
  actualRealTensorAssembly (fun i j => -Complex.I * H i j)

theorem actualImaginaryTensorAssembly_basis (H : CMatrix) (i j : Fin (m+1)) :
    actualImaginaryTensorAssembly H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      (H i j).im := by
  rw [actualImaginaryTensorAssembly, actualRealTensorAssembly_basis]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, zero_mul, neg_mul, one_mul, zero_sub, neg_neg]

theorem actual_modulated_forcing_tensor_real_imag (H : CMatrix) (theta : ℝ) :
    actualRealTensorAssembly (fun i j => incrementsMeanPhase theta * H i j) =
      Real.cos theta • actualRealTensorAssembly H -
        Real.sin theta • actualImaginaryTensorAssembly H := by
  apply actual_bilinear_tensor_eq_of_basis
  intro i j
  simp only [actualRealTensorAssembly_basis, actualImaginaryTensorAssembly_basis,
    sub_apply, smul_apply, smul_eq_mul]
  change (Complex.exp ((theta : ℂ) * Complex.I) * H i j).re = _
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

def actualSecondaryReturnedForcing
    (e : OpenPartialHomeomorph X X) (cutoff : X → ℝ) (HR HI : X → Tensor) (tau : ℝ) : X → Tensor :=
  fun z => if z ∈ e.source then
    (actualSecondaryLocalForcingTensor
      (actualSecondaryInverseForcing e cutoff HR) (actualSecondaryInverseForcing e cutoff HI)
      tau (e z)).bilinearComp (actualJointSpatialJacobian e z) (actualJointSpatialJacobian e z)
    else 0

theorem actual_secondary_returned_forcing_eq
    (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ ∞ e e.source) (hinv : ContDiffOn ℝ ∞ e.symm e.target)
    (hfirst : ∀ y ∈ e.source, (e y).1 = y.1)
    (HR HI : X → Tensor) (cutoff phase : X → ℝ)
    (hsupport : tsupport cutoff ⊆ e.source)
    (hadapted : ∀ y ∈ e.source, (e y).2 0 = phase y)
    (tau : ℝ) (z : X) :
    actualSecondaryReturnedForcing e cutoff HR HI tau z =
      cutoff z • (Real.cos (phase z / tau) • HR z - Real.sin (phase z / tau) • HI z) := by
  unfold actualSecondaryReturnedForcing
  split_ifs with hz
  · exact actual_secondary_forcing_pullback_cancel e he hinv hfirst HR HI cutoff phase hadapted tau z hz
  · have hcutoff : cutoff z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hsupport h))
    rw [hcutoff]
    ext v w
    simp only [smul_apply, smul_eq_mul, zero_apply, zero_mul]

/-- Only support at the actual observation point is needed. This avoids imposing
an artificial condition outside the target of a partial observation chart. -/
theorem actual_secondary_returned_forcing_eq_at
    (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ ∞ e e.source) (hinv : ContDiffOn ℝ ∞ e.symm e.target)
    (hfirst : ∀ y ∈ e.source, (e y).1 = y.1)
    (HR HI : X → Tensor) (cutoff phase : X → ℝ)
    (hadapted : ∀ y ∈ e.source, (e y).2 0 = phase y)
    (tau : ℝ) (z : X) (hsupport : cutoff z ≠ 0 → z ∈ e.source) :
    actualSecondaryReturnedForcing e cutoff HR HI tau z =
      cutoff z • (Real.cos (phase z / tau) • HR z - Real.sin (phase z / tau) • HI z) := by
  unfold actualSecondaryReturnedForcing
  split_ifs with hz
  · exact actual_secondary_forcing_pullback_cancel e he hinv hfirst HR HI cutoff phase hadapted tau z hz
  · have hcutoff : cutoff z = 0 := not_not.mp (fun hn => hz (hsupport hn))
    rw [hcutoff]
    ext v w
    simp only [smul_apply, smul_eq_mul, zero_apply, zero_mul]

theorem actual_secondary_forcing_partition_sum_at
    {Sub : Type*} [Fintype Sub]
    (e : Sub → OpenPartialHomeomorph X X)
    (he : ∀ a, ContDiffOn ℝ ∞ (e a) (e a).source)
    (hinv : ∀ a, ContDiffOn ℝ ∞ (e a).symm (e a).target)
    (hfirst : ∀ a y, y ∈ (e a).source → ((e a) y).1 = y.1)
    (HR HI : X → Tensor) (cutoff : Sub → X → ℝ) (phase : X → ℝ)
    (hadapted : ∀ a y, y ∈ (e a).source → ((e a) y).2 0 = phase y)
    (tau : ℝ) (z : X)
    (hsupport : ∀ a, cutoff a z ≠ 0 → z ∈ (e a).source)
    (hpartition : HR z ≠ 0 ∨ HI z ≠ 0 → ∑ a, cutoff a z = 1) :
    (∑ a, actualSecondaryReturnedForcing (e a) (cutoff a) HR HI tau z) =
      Real.cos (phase z / tau) • HR z - Real.sin (phase z / tau) • HI z := by
  simp_rw [actual_secondary_returned_forcing_eq_at (e _) (he _) (hinv _) (hfirst _) HR HI
    (cutoff _) phase (hadapted _) tau z (hsupport _)]
  rw [← Finset.sum_smul]
  by_cases h : HR z ≠ 0 ∨ HI z ≠ 0
  · rw [hpartition h, one_smul]
  · have hR : HR z = 0 := not_not.mp (not_or.mp h).1
    have hI : HI z = 0 := not_not.mp (not_or.mp h).2
    rw [hR, hI]
    ext v w
    simp only [smul_apply, sub_apply, smul_eq_mul, zero_apply, mul_zero, sub_self]

theorem actual_secondary_forcing_partition_sum
    {Sub : Type*} [Fintype Sub]
    (e : Sub → OpenPartialHomeomorph X X)
    (he : ∀ a, ContDiffOn ℝ ∞ (e a) (e a).source)
    (hinv : ∀ a, ContDiffOn ℝ ∞ (e a).symm (e a).target)
    (hfirst : ∀ a y, y ∈ (e a).source → ((e a) y).1 = y.1)
    (HR HI : X → Tensor) (cutoff : Sub → X → ℝ) (phase : X → ℝ)
    (hsupport : ∀ a, tsupport (cutoff a) ⊆ (e a).source)
    (hadapted : ∀ a y, y ∈ (e a).source → ((e a) y).2 0 = phase y)
    (tau : ℝ) (z : X)
    (hpartition : HR z ≠ 0 ∨ HI z ≠ 0 → ∑ a, cutoff a z = 1) :
    (∑ a, actualSecondaryReturnedForcing (e a) (cutoff a) HR HI tau z) =
      Real.cos (phase z / tau) • HR z - Real.sin (phase z / tau) • HI z := by
  simp_rw [actual_secondary_returned_forcing_eq (e _) (he _) (hinv _) (hfirst _) HR HI
    (cutoff _) phase (hsupport _) (hadapted _) tau z]
  rw [← Finset.sum_smul]
  by_cases h : HR z ≠ 0 ∨ HI z ≠ 0
  · rw [hpartition h, one_smul]
  · have hR : HR z = 0 := not_not.mp (not_or.mp h).1
    have hI : HI z = 0 := not_not.mp (not_or.mp h).2
    rw [hR, hI]
    ext v w
    simp only [smul_apply, sub_apply, smul_eq_mul, zero_apply, mul_zero, sub_self]

/-- The ordinary partition recovers the literal original nonzero quadratic
forcing tensor extracted from the same primary derivative coefficients. -/
theorem actual_secondary_quadratic_forcing_partition
    {Label SubPrimary SubSecondary : Type*} [Fintype SubPrimary] [Fintype SubSecondary]
    {N : ℕ}
    (phi : Label → Ep → D → ℝ) (tau : ℝ) (chi : Label → Ep → SubPrimary → D → ℝ)
    (P Q : Label → Ep → SubPrimary → D → EuclideanSpace ℝ (Fin N))
    (r : (Label × Label) × Fin 4)
    (e : SubSecondary → OpenPartialHomeomorph X X)
    (he : ∀ a, ContDiffOn ℝ ∞ (e a) (e a).source)
    (hinv : ∀ a, ContDiffOn ℝ ∞ (e a).symm (e a).target)
    (hfirst : ∀ a y, y ∈ (e a).source → ((e a) y).1 = y.1)
    (cutoff : SubSecondary → X → ℝ)
    (hsupport : ∀ a, tsupport (cutoff a) ⊆ (e a).source)
    (hadapted : ∀ a y, y ∈ (e a).source →
      ((e a) y).2 0 = incrementsSecondaryQuadraticPhase phi r.1.1 r.1.2 r.2 y)
    (z : X) :
    let H := incrementsSecondaryQuadraticForcing phi tau chi P Q
      (fun i _ => EuclideanSpace.single i 1) r.1.1 r.1.2 r.2
    let HR := fun y => actualRealTensorAssembly (H y)
    let HI := fun y => actualImaginaryTensorAssembly (H y)
    (HR z ≠ 0 ∨ HI z ≠ 0 → ∑ a, cutoff a z = 1) →
    (∑ a, actualSecondaryReturnedForcing (e a) (cutoff a) HR HI tau z) =
      actualSecondaryForcingTensor phi tau chi P Q r z := by
  intro H HR HI hpartition
  rw [actual_secondary_forcing_partition_sum e he hinv hfirst HR HI cutoff
    (incrementsSecondaryQuadraticPhase phi r.1.1 r.1.2 r.2) hsupport hadapted tau z hpartition]
  exact (actual_modulated_forcing_tensor_real_imag (H z)
    (incrementsSecondaryQuadraticPhase phi r.1.1 r.1.2 r.2 z / tau)).symm

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_forcing_partition_sum
#print axioms GlobalEmbedding.Continuation.actual_secondary_quadratic_forcing_partition
