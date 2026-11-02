import NormalPolar.ConstructionPositiveBranch

/-!
# Quadratic closeness of the true normal compression

The old-normal compression differs from identity by the compression of the
squared projection defect. Consequently its inverse reserve is 1-epsilon²,
which is stronger than the generic 1-epsilon bound for an arbitrary nearby
ambient operator. The operators below remain the original actual compression
and its native inverse.
-/

noncomputable section
open Set
open scoped ContDiff

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Continuation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

private noncomputable local instance quantitativeAmbientSemi : SeminormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance quantitativeAmbientNormed : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance quantitativeAmbientSpace : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance quantitativeFiberSemi (K : Submodule ℝ V) :
    SeminormedAddCommGroup (K →L[ℝ] K) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance quantitativeFiberNormed (K : Submodule ℝ V) :
    NormedAddCommGroup (K →L[ℝ] K) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance quantitativeFiberSpace (K : Submodule ℝ V) :
    NormedSpace ℝ (K →L[ℝ] K) := ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ V] in
/-- A norm reserve about identity gives the genuine coercivity estimate. -/
theorem operator_coercive_of_norm_sub_one_le
    (A : V →L[ℝ] V) (epsilon : ℝ) (hA : ‖A - 1‖ ≤ epsilon) (v : V) :
    (1 - epsilon) * ‖v‖ ^ 2 ≤ inner ℝ v (A v) := by
  have hn : ‖(A - 1) v‖ ≤ epsilon * ‖v‖ :=
    ((A - 1).le_opNorm v).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg v))
  have hi := real_inner_le_norm (-v) ((A - 1) v)
  rw [inner_neg_left, norm_neg] at hi
  have he : inner ℝ v ((A - 1) v) = inner ℝ v (A v) - ‖v‖ ^ 2 := by
    change inner ℝ v (A v - v) = _
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [he] at hi
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg v)
  nlinarith

/-- The actual inverse of a finite-dimensional near-identity operator is
constructed from coercivity; no inverse or its norm is a hypothesis. -/
theorem operator_inverse_bound_of_norm_sub_one_le
    (A : V →L[ℝ] V) (epsilon : ℝ) (hepsilon : epsilon < 1)
    (hA : ‖A - 1‖ ≤ epsilon) :
    A.IsInvertible ∧ ‖A.inverse‖ ≤ (1 - epsilon)⁻¹ := by
  have h := coercive_inverse_smooth_bound (Set.univ : Set ℝ) isOpen_univ
    (fun _ : ℝ ↦ A) (1 - epsilon) (sub_pos.mpr hepsilon) contDiffOn_const
    (fun _ _ v ↦ operator_coercive_of_norm_sub_one_le A epsilon hA v)
  exact h.1 0 (Set.mem_univ 0)

/-- The identity difference is exactly the squared true projection defect,
compressed to the old normal fiber. -/
theorem normalProjectionCompression_sub_one_eq_defect
    (K L : Submodule ℝ V) :
    normalProjectionCompression K L.starProjection - 1 =
      -normalProjectionCompression K (projectionDefect K.starProjection L.starProjection) := by
  rw [← normalProjectionCompression_one_sub_defect K L]
  have he : normalProjectionCompression K
      (1 - projectionDefect K.starProjection L.starProjection) =
      1 - normalProjectionCompression K (projectionDefect K.starProjection L.starProjection) := by
    rw [← normalProjectionCompression_one K]
    exact (normalProjectionCompressionL K).map_sub _ _
  rw [he]
  abel

/-- Orthogonal projections give quadratic, rather than merely linear,
compression closeness on the genuine old normal fiber. -/
theorem normalProjectionCompression_quadratic_gap
    (K L : Submodule ℝ V) :
    ‖normalProjectionCompression K L.starProjection - 1‖ ≤
      ‖K.starProjection - L.starProjection‖ ^ 2 := by
  rw [normalProjectionCompression_sub_one_eq_defect, norm_neg]
  exact (normalProjectionCompression_norm_le K _).trans
    (by simpa only [projectionDefect, pow_two] using
      norm_mul_le (K.starProjection - L.starProjection) (K.starProjection - L.starProjection))

/-- The true compression inverse has the explicit quadratic reserve. -/
theorem normalProjectionCompression_inverse_quadratic_bound
    (K L : Submodule ℝ V) (epsilon : ℝ) (hepsilon : epsilon < 1)
    (hgap : ‖K.starProjection - L.starProjection‖ ≤ epsilon) :
    (normalProjectionCompression K L.starProjection).IsInvertible ∧
      ‖(normalProjectionCompression K L.starProjection).inverse‖ ≤ (1 - epsilon ^ 2)⁻¹ := by
  have he0 : 0 ≤ epsilon := (norm_nonneg _).trans hgap
  have he2 : epsilon ^ 2 < 1 := by nlinarith
  apply operator_inverse_bound_of_norm_sub_one_le _ (epsilon ^ 2) he2
  exact (normalProjectionCompression_quadratic_gap K L).trans
    ((sq_le_sq₀ (norm_nonneg _) he0).mpr hgap)

/-- The actual inverse is quadratically close to identity, with an explicit
constant on the supplied reserve. -/
theorem normalProjectionCompression_inverse_quadratic_gap
    (K L : Submodule ℝ V) (epsilon : ℝ) (hepsilon : epsilon < 1)
    (hgap : ‖K.starProjection - L.starProjection‖ ≤ epsilon) :
    ‖(normalProjectionCompression K L.starProjection).inverse - 1‖ ≤
      (1 - epsilon ^ 2)⁻¹ * epsilon ^ 2 := by
  let G := normalProjectionCompression K L.starProjection
  obtain ⟨hG, hb⟩ := normalProjectionCompression_inverse_quadratic_bound K L epsilon hepsilon hgap
  have he0 : 0 ≤ epsilon := (norm_nonneg _).trans hgap
  have he2 : epsilon ^ 2 < 1 := by nlinarith
  have hd : ‖1 - G‖ ≤ epsilon ^ 2 := by
    rw [norm_sub_rev]
    exact (normalProjectionCompression_quadratic_gap K L).trans
      ((sq_le_sq₀ (norm_nonneg _) he0).mpr hgap)
  have hid : G.inverse - 1 = G.inverse * (1 - G) := by
    rw [mul_sub, mul_one]
    have hGI : G.inverse * G = 1 := hG.inverse_comp_self
    rw [hGI]
  rw [hid]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hb hd (norm_nonneg _) (inv_nonneg.mpr (sub_nonneg.mpr he2.le)))

/-- A fixed reserve controls the inverse while the actual projection gap
retains its quadratic size. -/
theorem normalProjectionCompression_inverse_gap_on_reserve
    (K L : Submodule ℝ V) (q : ℝ) (hq : q < 1)
    (hgap : ‖K.starProjection - L.starProjection‖ ≤ q) :
    ‖(normalProjectionCompression K L.starProjection).inverse - 1‖ ≤
      (1 - q ^ 2)⁻¹ * ‖K.starProjection - L.starProjection‖ ^ 2 := by
  let G := normalProjectionCompression K L.starProjection
  obtain ⟨hG, hb⟩ := normalProjectionCompression_inverse_quadratic_bound K L q hq hgap
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hgap
  have hq2 : q ^ 2 < 1 := by nlinarith
  have hd : ‖1 - G‖ ≤ ‖K.starProjection - L.starProjection‖ ^ 2 := by
    rw [norm_sub_rev]
    exact normalProjectionCompression_quadratic_gap K L
  have hid : G.inverse - 1 = G.inverse * (1 - G) := by
    rw [mul_sub, mul_one]
    have hGI : G.inverse * G = 1 := hG.inverse_comp_self
    rw [hGI]
  rw [hid]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hb hd (norm_nonneg _) (inv_nonneg.mpr (sub_nonneg.mpr hq2.le)))

end GlobalEmbedding.NormalPolar
