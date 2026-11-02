import GlobalEmbedding.Paper.MatrixCompactPositiveOperatorBound
import GlobalEmbedding.Paper.PointwiseJetNormalBound
import GlobalEmbedding.Paper.NormalProjectionGramFormula
import GlobalEmbedding.Paper.SmoothFrameNormalProjection
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Genuine uniform mixed-frame perturbation and buffered active pivots

Source: `literature/parallelizable-stable-plus-one/main.tex`, thm:free, lines455–470.
DAG: free-compact-pivot-perturbation. W3 registered this exact source before edits.
-/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace GlobalEmbedding.Paper

/-- The literal mixed-column perturbation, before choosing one common delta. -/
def freeMixedFrame {P E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A R : P → E →L[ℝ] F) (δ : ℝ) (p : P) : E →L[ℝ] F := A p + δ • R p

/-- The actual orthogonal projection of the unit complementary direction off
these genuine mixed columns. The Gram formula is proved below, not assumed. -/
def freeMixedNormal {P E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (A R : P → E →L[ℝ] F) (u : P → F) (δ : ℝ) (p : P) : F :=
  (LinearMap.range (freeMixedFrame A R δ p).toLinearMap)ᗮ.starProjection (u p)

/-- Genuine compact injective frame fields have a common positive squared lower
bound, by the already accepted actual positive-Gram compactness theorem. -/
theorem free_compact_frame_lower_bound {P E F : Type*} [TopologicalSpace P]
    [CompactSpace P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (A : P → E →L[ℝ] F) (hA : Continuous A)
    (hinj : ∀ p, Function.Injective (A p)) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ p v, lam * ‖v‖ ^ 2 ≤ ‖A p v‖ ^ 2 := by
  have hG : Continuous (fun p ↦ (A p).adjoint.comp (A p)) :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).continuous.comp hA).clm_comp hA
  have hpos (p : P) (v : E) (hv : v ≠ 0) :
      0 < ⟪((A p).adjoint.comp (A p)) v, v⟫ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (by simpa only [map_zero] using (hinj p).ne hv))
  obtain ⟨lam, hlam, hb⟩ := compact_positive_operator_lower_bound
    (isCompact_univ : IsCompact (univ : Set P))
    (fun p ↦ (A p).adjoint.comp (A p)) hG.continuousOn (fun p _ v hv ↦ hpos p v hv)
  refine ⟨lam, hlam, ?_⟩
  intro p v
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq] using hb p (mem_univ p) v

/-- The actual projected direction equals the genuine inverse-Gram expression
u−M(M* M)⁻¹M*u whenever the actual mixed frame is injective. -/
theorem freeMixedNormal_gram {P E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (A R : P → E →L[ℝ] F)
    (u : P → F) (δ : ℝ) (p : P) (hinj : Function.Injective (freeMixedFrame A R δ p)) :
    freeMixedNormal A R u δ p = u p - freeMixedFrame A R δ p
      (((freeMixedFrame A R δ p).adjoint.comp (freeMixedFrame A R δ p)).inverse
        ((freeMixedFrame A R δ p).adjoint (u p))) := by
  rw [freeMixedNormal, (normal_projection_gram_formula _ hinj).2.2.2]
  rfl

/-- One common delta-neighborhood preserves a genuine positive mixed-frame
margin on the entire compact parameter space. The actual projected direction
moves by at most C abs(delta), with no assumption of perturbed injectivity. -/
theorem free_compact_mixed_projection_bound {P E F : Type*} [TopologicalSpace P]
    [CompactSpace P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (A R : P → E →L[ℝ] F) (u : P → F)
    (hA : Continuous A) (hR : Continuous R) (hinj : ∀ p, Function.Injective (A p))
    (hu : ∀ p, ‖u p‖ ≤ 1)
    (hperp : ∀ p, u p ∈ (LinearMap.range (A p).toLinearMap)ᗮ) :
    ∃ ε lam C : ℝ, 0 < ε ∧ 0 < lam ∧ 0 < C ∧ ∀ δ : ℝ, |δ| ≤ ε → ∀ p : P,
      (∀ v : E, lam * ‖v‖ ^ 2 ≤ ‖freeMixedFrame A R δ p v‖ ^ 2) ∧
      ‖freeMixedNormal A R u δ p - u p‖ ≤ C * |δ| := by
  obtain ⟨lam, hlam, hbase⟩ := free_compact_frame_lower_bound A hA hinj
  obtain ⟨B, hB⟩ := (isCompact_univ : IsCompact (univ : Set P))
    |>.exists_bound_of_continuousOn hR.continuousOn
  let L := max 1 B
  have hL : 0 < L := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hRb (p) : ‖R p‖ ≤ L := (hB p (mem_univ p)).trans (le_max_right _ _)
  let ε := Real.sqrt lam / (2 * L)
  let C := (3 / Real.sqrt lam) * L
  have hε : 0 < ε := div_pos (Real.sqrt_pos.mpr hlam) (by positivity)
  have hC : 0 < C := mul_pos (div_pos (by norm_num) (Real.sqrt_pos.mpr hlam)) hL
  refine ⟨ε, lam / 4, C, hε, by positivity, hC, ?_⟩
  intro δ hδ p
  have hdist : ‖A p - freeMixedFrame A R δ p‖ ≤ |δ| * L := by
    have he : A p - freeMixedFrame A R δ p = -(δ • R p) := by
      dsimp [freeMixedFrame]
      abel
    rw [he, norm_neg, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hRb p) (abs_nonneg _)
  have hsmall : |δ| * L ≤ Real.sqrt lam / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * L)).mp hδ
    nlinarith
  have hp := pointwise_projected_jet_estimate (A p) (freeMixedFrame A R δ p)
    (ContinuousLinearMap.id ℝ F) (ContinuousLinearMap.id ℝ F)
    lam 1 hlam (hbase p) (hdist.trans hsmall) ContinuousLinearMap.norm_id_le
  have hgap : ‖(LinearMap.range (freeMixedFrame A R δ p).toLinearMap)ᗮ.starProjection -
      (LinearMap.range (A p).toLinearMap)ᗮ.starProjection‖ ≤
      (3 / Real.sqrt lam) * ‖A p - freeMixedFrame A R δ p‖ := by
    simpa only [ContinuousLinearMap.comp_id, sub_self, norm_zero, zero_add, mul_one] using hp.2
  have hu0 : (LinearMap.range (A p).toLinearMap)ᗮ.starProjection (u p) = u p :=
    Submodule.starProjection_eq_self_iff.mpr (hperp p)
  refine ⟨hp.1, ?_⟩
  calc
    ‖freeMixedNormal A R u δ p - u p‖ =
        ‖((LinearMap.range (freeMixedFrame A R δ p).toLinearMap)ᗮ.starProjection -
          (LinearMap.range (A p).toLinearMap)ᗮ.starProjection) (u p)‖ := by
      rw [sub_apply, hu0]
      rfl
    _ ≤ ‖(LinearMap.range (freeMixedFrame A R δ p).toLinearMap)ᗮ.starProjection -
          (LinearMap.range (A p).toLinearMap)ᗮ.starProjection‖ * ‖u p‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (3 / Real.sqrt lam) * (|δ| * L) * 1 :=
      mul_le_mul (hgap.trans (mul_le_mul_of_nonneg_left hdist (by positivity)))
        (hu p) (norm_nonneg _) (by positivity)
    _ = C * |δ| := by dsimp [C]; ring

/-- The genuine normal projector is continuous for an actual continuous injective
frame field on an arbitrary topological parameter space. The inverse-Gram map
is evaluated only at its genuinely invertible values. -/
theorem free_frame_normal_projection_continuous {P E F : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : P → E →L[ℝ] F) (hA : Continuous A) (hinj : ∀ p, Function.Injective (A p)) :
    Continuous (fun p ↦ (LinearMap.range (A p).toLinearMap)ᗮ.starProjection) := by
  have hadj := (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).continuous.comp hA
  have hGram : Continuous (fun p : P ↦ (A p).adjoint.comp (A p)) :=
    hadj.clm_comp hA
  have hInv : Continuous (fun p ↦ ((A p).adjoint.comp (A p)).inverse) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hG := (frame_gram_positive_invertible (A p) (hinj p)).2.2
    have hi : ContinuousAt (fun B : E →L[ℝ] E ↦ B.inverse) ((A p).adjoint.comp (A p)) :=
      (hG.contDiffAt_map_inverse (n := 0)).continuousAt
    exact ContinuousAt.comp (f := fun q : P ↦ (A q).adjoint.comp (A q))
      (x := p) hi hGram.continuousAt
  have hh := (continuous_const (y := ContinuousLinearMap.id ℝ F)).sub
    (hA.clm_comp (hInv.clm_comp hadj))
  exact hh.congr (fun p ↦ (normal_projection_gram_formula (A p) (hinj p)).2.2.2.symm)

/-- A strict pivot margin on actual curvature zero extends to one genuine
curvature buffer over the entire compact parameter space. The proof takes the
positive minimum of abs(curvature) on the compact bad-pivot set, never a quotient
by curvature and never point-dependent radii. -/
theorem free_compact_curvature_buffer {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (κ pivot : P → ℝ) (hκ : Continuous κ) (hp : Continuous pivot)
    (a b : ℝ) (hab : a < b) (hzero : ∀ p, κ p = 0 → b ≤ pivot p) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ p, |κ p| < d₀ → a ≤ pivot p := by
  let K : Set P := {p | pivot p ≤ a}
  have hK : IsCompact K := by
    simpa only [univ_inter] using
      (isCompact_univ : IsCompact (univ : Set P)).inter_right
        (isClosed_le hp (continuous_const (y := a)))
  have hn (p : P) (hpK : p ∈ K) : κ p ≠ 0 := by
    intro hz
    have hh := hzero p hz
    have hpa : pivot p ≤ a := hpK
    linarith
  by_cases hne : K.Nonempty
  · obtain ⟨p, hpK, hmin⟩ := hK.exists_isMinOn hne hκ.abs.continuousOn
    refine ⟨|κ p|, abs_pos.mpr (hn p hpK), ?_⟩
    intro x hx
    by_contra hbad
    have hxK : x ∈ K := (lt_of_not_ge hbad).le
    exact (not_lt_of_ge (hmin hxK)) hx
  · refine ⟨1, one_pos, ?_⟩
    intro p hp₀
    by_contra hbad
    exact hne ⟨p, (lt_of_not_ge hbad).le⟩

/-- The full compact perturbation mechanism for the actual mixed active pivot.
The active vector genuinely factors as delta*b at curvature zero and its
unprojected pairing is delta. The constructed delta0 is common to all points;
the quadratic projection error and the curvature buffer are derived, not input. -/
theorem free_compact_pivot_choice {P E F : Type*} [TopologicalSpace P] [CompactSpace P]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A R : P → E →L[ℝ] F) (u b : P → F) (B : ℝ → P → F) (κ : P → ℝ)
    (hA : Continuous A) (hR : Continuous R) (hu : Continuous u) (hb : Continuous b)
    (hB : ∀ δ, Continuous (B δ)) (hκ : Continuous κ)
    (hinj : ∀ p, Function.Injective (A p)) (hunit : ∀ p, ‖u p‖ ≤ 1)
    (hperp : ∀ p, u p ∈ (LinearMap.range (A p).toLinearMap)ᗮ)
    (hfactor : ∀ δ p, κ p = 0 → B δ p = δ • b p)
    (hpivot : ∀ p, κ p = 0 → ⟪u p, b p⟫ = 1) :
    ∃ δ₀ d₀ lam C : ℝ, 0 < δ₀ ∧ 0 < d₀ ∧ 0 < lam ∧ 0 < C ∧ ∀ p : P,
      (∀ v : E, lam * ‖v‖ ^ 2 ≤ ‖freeMixedFrame A R δ₀ p v‖ ^ 2) ∧
      ‖freeMixedNormal A R u δ₀ p - u p‖ ≤ C * δ₀ ∧
      (κ p = 0 → |⟪freeMixedNormal A R u δ₀ p, B δ₀ p⟫ - δ₀| ≤ C * δ₀ ^ 2) ∧
      (|κ p| < d₀ → δ₀ / 4 ≤ ⟪freeMixedNormal A R u δ₀ p, B δ₀ p⟫) := by
  obtain ⟨ε, lam, C₀, hε, hlam, hC₀, hproj⟩ :=
    free_compact_mixed_projection_bound A R u hA hR hinj hunit hperp
  obtain ⟨B₀, hB₀⟩ := (isCompact_univ : IsCompact (univ : Set P))
    |>.exists_bound_of_continuousOn hb.continuousOn
  let L := max 1 B₀
  have hL : 0 < L := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hbnd (p) : ‖b p‖ ≤ L := (hB₀ p (mem_univ p)).trans (le_max_right _ _)
  let C := C₀ * L
  have hC : 0 < C := mul_pos hC₀ hL
  have hCC : C₀ ≤ C := by
    calc
      C₀ = C₀ * 1 := (mul_one _).symm
      _ ≤ C₀ * L := mul_le_mul_of_nonneg_left (le_max_left _ _) hC₀.le
  let δ₀ := min ε (1 / (2 * (C + 1)))
  have hδ : 0 < δ₀ := lt_min hε (by positivity)
  have hδε : |δ₀| ≤ ε := by rw [abs_of_pos hδ]; exact min_le_left _ _
  have hsmall : C * δ₀ ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (C + 1))).mp
      (min_le_right ε (1 / (2 * (C + 1))))
    change δ₀ * (2 * (C + 1)) ≤ 1 at hh
    nlinarith
  have hquadratic : C * δ₀ ^ 2 ≤ δ₀ / 2 := by
    have hh := mul_le_mul_of_nonneg_right hsmall hδ.le
    nlinarith
  have hframes (p) := hproj δ₀ hδε p
  have hMinj (p : P) : Function.Injective (freeMixedFrame A R δ₀ p) := by
    intro v w hvw
    apply sub_eq_zero.mp
    have hh := (hframes p).1 (v - w)
    have hz : freeMixedFrame A R δ₀ p (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    rw [hz, norm_zero, zero_pow (by omega)] at hh
    have hs : ‖v - w‖ ^ 2 ≤ 0 :=
      (mul_le_mul_iff_of_pos_left hlam).mp (by simpa using hh)
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (v - w)])
  have hMc : Continuous (fun p ↦ freeMixedFrame A R δ₀ p) :=
    hA.fun_add ((continuous_const (y := δ₀)).fun_smul hR)
  have hnormal : Continuous (fun p ↦ freeMixedNormal A R u δ₀ p) :=
    (free_frame_normal_projection_continuous _ hMc hMinj).clm_apply hu
  let pivot := fun p ↦ ⟪freeMixedNormal A R u δ₀ p, B δ₀ p⟫
  have hpcont : Continuous pivot := hnormal.inner (hB δ₀)
  have herror (p : P) (hz : κ p = 0) : |pivot p - δ₀| ≤ C * δ₀ ^ 2 := by
    have huB : ⟪u p, B δ₀ p⟫ = δ₀ := by
      rw [hfactor δ₀ p hz, real_inner_smul_right, hpivot p hz, mul_one]
    have heq : pivot p - δ₀ =
        ⟪freeMixedNormal A R u δ₀ p - u p, B δ₀ p⟫ := by
      rw [inner_sub_left, huB]
    have hBp : ‖B δ₀ p‖ ≤ δ₀ * L := by
      rw [hfactor δ₀ p hz, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      exact mul_le_mul_of_nonneg_left (hbnd p) hδ.le
    calc
      |pivot p - δ₀| = |⟪freeMixedNormal A R u δ₀ p - u p, B δ₀ p⟫| := congrArg abs heq
      _ ≤ ‖freeMixedNormal A R u δ₀ p - u p‖ * ‖B δ₀ p‖ := abs_real_inner_le_norm _ _
      _ ≤ (C₀ * δ₀) * (δ₀ * L) := mul_le_mul
        (by simpa only [abs_of_pos hδ] using (hframes p).2) hBp (norm_nonneg _)
        (mul_nonneg hC₀.le hδ.le)
      _ = C * δ₀ ^ 2 := by dsimp [C]; ring
  have hzero (p : P) (hz : κ p = 0) : δ₀ / 2 ≤ pivot p := by
    have hh := (abs_le.mp (herror p hz)).1
    linarith
  obtain ⟨d₀, hd₀, hbuffer⟩ := free_compact_curvature_buffer κ pivot hκ hpcont
    (δ₀ / 4) (δ₀ / 2) (by linarith) hzero
  refine ⟨δ₀, d₀, lam, C, hδ, hd₀, hlam, hC, ?_⟩
  intro p
  refine ⟨(hframes p).1, ?_, herror p, hbuffer p⟩
  have hh : ‖freeMixedNormal A R u δ₀ p - u p‖ ≤ C₀ * δ₀ := by
    simpa only [abs_of_pos hδ] using (hframes p).2
  exact hh.trans (mul_le_mul_of_nonneg_right hCC hδ.le)

end GlobalEmbedding.Paper
