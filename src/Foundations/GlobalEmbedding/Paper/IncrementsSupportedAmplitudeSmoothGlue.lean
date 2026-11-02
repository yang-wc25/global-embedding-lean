import GlobalEmbedding.Paper.IncrementsPositiveReserveAmplitude

/-!
# Original supported positive-reserve amplitude: joint smooth glue

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines594–609,638–673.
The source D may be the full source/parameter product. Only the actual cutoff
tsupport requires positive reserve. All formulas below are the original functions;
no extension, alternate amplitude, norm or compact source is introduced.
-/

open scoped ContDiff Topology
open Set

namespace GlobalEmbedding.Paper

section JointSource

variable {D E F : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The genuine positive-argument open contains the original cutoff tsupport.
Its openness follows from the actual coefficient application on the original O. -/
theorem increments_supported_amplitude_positive_open
    (O : Set D) (hO : IsOpen O) (L : D → E →L[ℝ] ℝ) (A : D → E)
    (cutoff : D → ℝ) (hL : ContDiffOn ℝ ∞ L O) (hA : ContDiffOn ℝ ∞ A O)
    (hcutoffO : tsupport cutoff ⊆ O) (c : ℝ) (hc : 0 < c)
    (hreserve : ∀ x ∈ tsupport cutoff, c ≤ L x (A x)) :
    IsOpen (O ∩ {x | 0 < L x (A x)}) ∧
      tsupport cutoff ⊆ O ∩ {x | 0 < L x (A x)} := by
  exact ⟨(hL.clm_apply hA).continuousOn.isOpen_inter_preimage hO isOpen_Ioi,
    fun x hx ↦ ⟨hcutoffO hx, hc.trans_le (hreserve x hx)⟩⟩

omit [NormedSpace ℝ D] in
/-- The literal amplitude is eventually zero off the cutoff tsupport, regardless
of the values or regularity of its square-root argument and normal there. -/
theorem increments_supported_amplitude_eventually_zero
    (L : D → E →L[ℝ] ℝ) (A : D → E) (cutoff : D → ℝ) (normal : D → F)
    {x : D} (hx : x ∉ tsupport cutoff) :
    (fun y ↦ (cutoff y * Real.sqrt (L y (A y))) • normal y) =ᶠ[𝓝 x]
      (fun _ ↦ (0 : F)) := by
  filter_upwards [(isClosed_tsupport cutoff).isOpen_compl.mem_nhds hx] with y hy
  rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_smul]

omit [NormedSpace ℝ D] in
/-- Native support multiplication and scalar multiplication preserve the actual
cutoff tsupport; no strict cutoff positivity or division is needed. -/
theorem increments_supported_amplitude_tsupport
    (L : D → E →L[ℝ] ℝ) (A : D → E) (cutoff : D → ℝ) (normal : D → F) :
    tsupport (fun y ↦ (cutoff y * Real.sqrt (L y (A y))) • normal y) ⊆
      tsupport cutoff := by
  exact (tsupport_smul_subset_left _ _).trans tsupport_mul_subset_left

/-- Global joint smoothness of the actual supported amplitude. On the original
cutoff tsupport use accepted local sqrt regularity; elsewhere native eventual
zero gives smoothness. Fields need only be smooth on the original open O. -/
theorem increments_supported_amplitude_contDiff
    (O : Set D) (hO : IsOpen O) (L : D → E →L[ℝ] ℝ) (A : D → E)
    (cutoff : D → ℝ) (normal : D → F)
    (hL : ContDiffOn ℝ ∞ L O) (hA : ContDiffOn ℝ ∞ A O)
    (hcutoff : ContDiffOn ℝ ∞ cutoff O) (hnormal : ContDiffOn ℝ ∞ normal O)
    (hcutoffO : tsupport cutoff ⊆ O) (c : ℝ) (hc : 0 < c)
    (hreserve : ∀ x ∈ tsupport cutoff, c ≤ L x (A x)) :
    ContDiff ℝ ∞ (fun y ↦ (cutoff y * Real.sqrt (L y (A y))) • normal y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport cutoff
  · exact increments_positive_reserve_amplitude_contDiffAt O hO L A cutoff normal
      hL hA hcutoff hnormal (hcutoffO hx) (hc.trans_le (hreserve x hx))
  · exact contDiffAt_const.congr_of_eventuallyEq
      (increments_supported_amplitude_eventually_zero L A cutoff normal hx)

end JointSource

/-- The SAME canonical original free amplitude is globally jointly smooth,
including delta=0, tau=0 and zero dimensions. Its original factor is retained. -/
theorem increments_supported_primary_free_amplitude_contDiff
    {n N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (O : Set (EuclideanSpace ℝ (Fin n))) (hO : IsOpen O)
    (L : EuclideanSpace ℝ (Fin n) → E →L[ℝ] ℝ) (A : EuclideanSpace ℝ (Fin n) → E)
    (cutoff : EuclideanSpace ℝ (Fin n) → ℝ)
    (normal : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (hL : ContDiffOn ℝ ∞ L O) (hA : ContDiffOn ℝ ∞ A O)
    (hcutoff : ContDiffOn ℝ ∞ cutoff O) (hnormal : ContDiffOn ℝ ∞ normal O)
    (hcutoffO : tsupport cutoff ⊆ O) (c : ℝ) (hc : 0 < c)
    (hreserve : ∀ x ∈ tsupport cutoff, c ≤ L x (A x)) (δ τ : ℝ) :
    ContDiff ℝ ∞ (incrementsPrimaryFreeAmplitude δ τ
      (fun y ↦ cutoff y * Real.sqrt (L y (A y))) normal) := by
  have h := (increments_supported_amplitude_contDiff O hO L A cutoff normal
    hL hA hcutoff hnormal hcutoffO c hc hreserve).const_smul (Real.sqrt 2 * δ * τ)
  change ContDiff ℝ ∞ (fun y ↦
    (Real.sqrt 2 * δ * τ * (cutoff y * Real.sqrt (L y (A y)))) • normal y)
  simpa only [incrementsPrimaryFreeAmplitude, smul_smul, smul_eq_mul] using h

/-- The original free amplitude stays inside the same cutoff tsupport for every
external scale, without excluding zero delta or zero tau. -/
theorem increments_supported_primary_free_amplitude_tsupport
    {n N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : EuclideanSpace ℝ (Fin n) → E →L[ℝ] ℝ) (A : EuclideanSpace ℝ (Fin n) → E)
    (cutoff : EuclideanSpace ℝ (Fin n) → ℝ)
    (normal : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N)) (δ τ : ℝ) :
    tsupport (incrementsPrimaryFreeAmplitude δ τ
      (fun y ↦ cutoff y * Real.sqrt (L y (A y))) normal) ⊆ tsupport cutoff := by
  exact (tsupport_smul_subset_left _ _).trans
    (tsupport_mul_subset_right.trans tsupport_mul_subset_left)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.increments_supported_amplitude_positive_open
#print axioms GlobalEmbedding.Paper.increments_supported_amplitude_eventually_zero
#print axioms GlobalEmbedding.Paper.increments_supported_amplitude_tsupport
#print axioms GlobalEmbedding.Paper.increments_supported_amplitude_contDiff
#print axioms GlobalEmbedding.Paper.increments_supported_primary_free_amplitude_contDiff
#print axioms GlobalEmbedding.Paper.increments_supported_primary_free_amplitude_tsupport
