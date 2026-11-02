import Probes.ActualFixedMetricNormalProjection
import Smoothing.WeightedActualOperations

/-!
# The actual normal-bundle compression has a quantitative inverse reserve

For the old normal space K and the actual new projection Pi, the compression
below is literally iota-adjoint * Pi * iota. Closeness of Pi to the old
projection produces its distance to identity and its coercivity. This is a
prerequisite for the orthogonal identification; it does not construct the
inverse square root or claim that the full identification is already proved.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private noncomputable local instance normalCompressionAmbientSemi : SeminormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance normalCompressionAmbientNormed : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance normalCompressionAmbientSpace : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance normalCompressionFiberSemi (K : Submodule ℝ V) : SeminormedAddCommGroup (K →L[ℝ] K) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance normalCompressionFiberNormed (K : Submodule ℝ V) : NormedAddCommGroup (K →L[ℝ] K) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance normalCompressionFiberSpace (K : Submodule ℝ V) : NormedSpace ℝ (K →L[ℝ] K) :=
  ContinuousLinearMap.toNormedSpace

def normalProjectionCompression (K : Submodule ℝ V) (Pi : V →L[ℝ] V) : K →L[ℝ] K :=
  K.orthogonalProjectionOnto.comp (Pi.comp K.subtypeL)

theorem normalProjectionCompression_eq_adjoint (K : Submodule ℝ V) (Pi : V →L[ℝ] V) :
    normalProjectionCompression K Pi = K.subtypeL.adjoint.comp (Pi.comp K.subtypeL) := by
  rw [Submodule.adjoint_subtypeL]
  rfl

theorem normalProjectionCompression_self (K : Submodule ℝ V) :
    normalProjectionCompression K K.starProjection = ContinuousLinearMap.id ℝ K := by
  ext v
  simp [normalProjectionCompression]

theorem normalProjectionCompression_norm_le (K : Submodule ℝ V) (Pi : V →L[ℝ] V) :
    ‖normalProjectionCompression K Pi‖ ≤ ‖Pi‖ := by
  unfold normalProjectionCompression
  calc
    _ ≤ ‖K.orthogonalProjectionOnto‖ * ‖Pi.comp K.subtypeL‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖Pi‖ * 1) := mul_le_mul K.orthogonalProjectionOnto_norm_le
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (Submodule.norm_subtypeL_le K) Pi.opNorm_nonneg))
      (Pi.comp K.subtypeL).opNorm_nonneg zero_le_one
    _ = _ := by ring

theorem normalProjectionCompression_sub_id (K : Submodule ℝ V) (Pi : V →L[ℝ] V) :
    normalProjectionCompression K Pi - ContinuousLinearMap.id ℝ K =
      normalProjectionCompression K (Pi - K.starProjection) := by
  rw [← normalProjectionCompression_self K]
  ext v
  simp [normalProjectionCompression]

/-- The genuine compression is as close to identity as the two projections. -/
theorem normalProjectionCompression_sub_id_norm_le (K : Submodule ℝ V) (Pi : V →L[ℝ] V) :
    ‖normalProjectionCompression K Pi - ContinuousLinearMap.id ℝ K‖ ≤ ‖Pi - K.starProjection‖ := by
  rw [normalProjectionCompression_sub_id]
  exact normalProjectionCompression_norm_le K _

/-- No output positivity is assumed: projection closeness gives the actual
compression reserve 1-epsilon, including the zero-dimensional normal space. -/
theorem normalProjectionCompression_coercive (K : Submodule ℝ V) (Pi : V →L[ℝ] V)
    (epsilon : ℝ) (hclose : ‖Pi - K.starProjection‖ ≤ epsilon) (v : K) :
    (1-epsilon) * ‖v‖^2 ≤ inner ℝ v (normalProjectionCompression K Pi v) := by
  let G := normalProjectionCompression K Pi
  let R := G - ContinuousLinearMap.id ℝ K
  have hb : ‖R‖ ≤ epsilon := (normalProjectionCompression_sub_id_norm_le K Pi).trans hclose
  have hv : ‖R v‖ ≤ epsilon * ‖v‖ :=
    (R.le_opNorm v).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg v))
  have hi : -(epsilon * ‖v‖^2) ≤ inner ℝ v (R v) := by
    have h := real_inner_le_norm (-v) (R v)
    rw [inner_neg_left, norm_neg] at h
    have hm := mul_le_mul_of_nonneg_left hv (norm_nonneg v)
    nlinarith
  calc
    _ = ‖v‖^2 - epsilon * ‖v‖^2 := by ring
    _ ≤ ‖v‖^2 + inner ℝ v (R v) := by linarith
    _ = inner ℝ v (G v) := by
      rw [← real_inner_self_eq_norm_sq, ← inner_add_right]
      congr 1
      simp [R]

/-- A smooth actual projection family close to the old one produces the
actual smooth inverse of iota-adjoint Pi iota, with a fixed uniform bound. -/
theorem normalProjectionCompression_inverse
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Submodule ℝ V) (Pi : X → V →L[ℝ] V) (O : Set X) (hO : IsOpen O)
    (hPi : ContDiffOn ℝ ∞ Pi O) (epsilon : ℝ) (hepsilon : epsilon < 1)
    (hclose : ∀ x ∈ O, ‖Pi x - K.starProjection‖ ≤ epsilon) :
    (∀ x ∈ O, (normalProjectionCompression K (Pi x)).IsInvertible ∧
      ‖(normalProjectionCompression K (Pi x)).inverse‖ ≤ (1-epsilon)⁻¹) ∧
    ContDiffOn ℝ ∞ (fun x => (normalProjectionCompression K (Pi x)).inverse) O := by
  apply coercive_inverse_smooth_bound O hO (fun x => normalProjectionCompression K (Pi x))
    (1-epsilon) (sub_pos.mpr hepsilon)
  · exact contDiffOn_const.clm_comp (hPi.clm_comp contDiffOn_const)
  · intro x hx v
    exact normalProjectionCompression_coercive K (Pi x) epsilon (hclose x hx) v

/-- The actual inverse reserve at a single point, without a supplied inverse. -/
theorem normalProjectionCompression_inverse_bound (K : Submodule ℝ V) (Pi : V →L[ℝ] V)
    (epsilon : ℝ) (hepsilon : epsilon < 1) (hclose : ‖Pi-K.starProjection‖ ≤ epsilon) :
    (normalProjectionCompression K Pi).IsInvertible ∧
      ‖(normalProjectionCompression K Pi).inverse‖ ≤ (1-epsilon)⁻¹ := by
  have h := normalProjectionCompression_inverse (X := ℝ) K (fun _ => Pi) Set.univ isOpen_univ
    contDiffOn_const epsilon hepsilon (fun _ _ => hclose)
  exact h.1 0 (Set.mem_univ 0)

/-- The inverse is O(epsilon) from identity for the actual compression. -/
theorem normalProjectionCompression_inverse_sub_id_norm_le
    (K : Submodule ℝ V) (Pi : V →L[ℝ] V) (epsilon : ℝ)
    (hepsilon : epsilon < 1) (hclose : ‖Pi-K.starProjection‖ ≤ epsilon) :
    ‖(normalProjectionCompression K Pi).inverse - ContinuousLinearMap.id ℝ K‖ ≤
      (1-epsilon)⁻¹ * epsilon := by
  let G := normalProjectionCompression K Pi
  obtain ⟨hG,hGb⟩ := normalProjectionCompression_inverse_bound K Pi epsilon hepsilon hclose
  change G.IsInvertible at hG
  have he : G.inverse - ContinuousLinearMap.id ℝ K =
      G.inverse.comp (ContinuousLinearMap.id ℝ K - G) := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id, hG.inverse_comp_self]
  rw [he]
  have hd : ‖ContinuousLinearMap.id ℝ K - G‖ ≤ epsilon := by
    rw [norm_sub_rev]
    exact (normalProjectionCompression_sub_id_norm_le K Pi).trans hclose
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hGb hd (ContinuousLinearMap.id ℝ K - G).opNorm_nonneg
      (inv_nonneg.mpr (sub_nonneg.mpr hepsilon.le)))

/-- Compression is an actual fixed continuous linear map on ambient operators. -/
def normalProjectionCompressionL (K : Submodule ℝ V) : (V →L[ℝ] V) →L[ℝ] (K →L[ℝ] K) :=
  LinearMap.mkContinuous
    { toFun := normalProjectionCompression K
      map_add' := by intro P Q; ext v; simp [normalProjectionCompression]
      map_smul' := by intro c P; ext v; simp [normalProjectionCompression] }
    1 (fun P => by simpa using normalProjectionCompression_norm_le K P)

theorem normalProjectionCompressionL_norm_le (K : Submodule ℝ V) :
    ‖normalProjectionCompressionL K‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The actual compression and its actual inverse inherit uniform joint slow
jets from the actual projection; no bound on either output field is assumed. -/
theorem normalProjectionCompression_inverse_slow_jets
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Submodule ℝ V) (Pi : X → V →L[ℝ] V) (O : Set X) (hO : IsOpen O)
    (hPi : ContDiffOn ℝ ∞ Pi O) (j : ℕ) (epsilon ell M : ℝ)
    (hepsilon : epsilon < 1) (hell : 0 < ell) (hM : 0 ≤ M)
    (hclose : ∀ x ∈ O, ‖Pi x - K.starProjection‖ ≤ epsilon)
    (hPij : ∀ k ≤ j, ∀ x ∈ O, ell^k * ‖iteratedFDeriv ℝ k Pi x‖ ≤ M) :
    (∀ x ∈ O, (normalProjectionCompression K (Pi x)).IsInvertible ∧
      ‖(normalProjectionCompression K (Pi x)).inverse‖ ≤ (1-epsilon)⁻¹) ∧
    ContDiffOn ℝ ∞ (fun x => (normalProjectionCompression K (Pi x)).inverse) O ∧
    ∀ k ≤ j, ∀ x ∈ O, ell^k *
      ‖iteratedFDeriv ℝ k (fun y => (normalProjectionCompression K (Pi y)).inverse) x‖ ≤
        slowInverseMajorant (1-epsilon)⁻¹ M j := by
  let L := normalProjectionCompressionL K
  have hP : ContDiffOn ℝ ∞ (fun x => normalProjectionCompression K (Pi x)) O :=
    L.contDiff.comp_contDiffOn hPi
  apply actual_coercive_inverse_slow_jets j O hO (fun x => normalProjectionCompression K (Pi x))
    hP (1-epsilon) ell M (sub_pos.mpr hepsilon) hell hM
  · intro x hx v
    exact normalProjectionCompression_coercive K (Pi x) epsilon (hclose x hx) v
  · intro k _ hk x hx
    have hb := slow_linear_jet_bound L O hO Pi hPi k ell M hell.le x hx (hPij k hk x hx)
    exact hb.trans (mul_le_of_le_one_left hM (normalProjectionCompressionL_norm_le K))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.normalProjectionCompression_sub_id_norm_le
#print axioms GlobalEmbedding.Continuation.normalProjectionCompression_coercive
#print axioms GlobalEmbedding.Continuation.normalProjectionCompression_inverse

#print axioms GlobalEmbedding.Continuation.normalProjectionCompression_inverse_slow_jets

#print axioms GlobalEmbedding.Continuation.normalProjectionCompression_inverse_sub_id_norm_le
