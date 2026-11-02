import GlobalEmbedding.Offline.CoincidenceDifferentialRank
import GlobalEmbedding.Paper.PointwiseJetNormalBound
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Actual paired value columns force the coincidence parameter-normal rank

Source: `prop:probes`, (8.1)–(8.2), and the final value operation in
`thm:upgrade`, main.tex line 1076. Only the LEADING wave at the second point
vanishes. Both actual global remainder values are retained below.

This is the quantitative consumer of genuine paired-probe response estimates.
It does not construct that probe family, its exact metric, its legal waves,
or the uniform normal-projection reserves. The actual derivative is the SAME
native `coincidenceParameterNormalDerivative` used by the avoidance endpoint.
-/

noncomputable section

open Function Filter Manifold Bundle Set GlobalEmbedding.Paper
open scoped Topology ContDiff

namespace GlobalEmbedding.Offline

section FiniteColumns

variable {r : ℕ} {V W P : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Native finite-dimensional independence gives a positive lower norm margin,
chosen before any fast angles or perturbation columns. This includes `r = 0`.
Source: the fixed principal value-frame margin in `thm:upgrade`. -/
theorem exists_positive_finite_frame_margin (v : Fin r → V)
    (hv : LinearIndependent ℝ v) :
    ∃ m : ℝ, 0 < m ∧ ∀ c : Fin r → ℝ, m * ‖c‖ ≤ ‖∑ i, c i • v i‖ := by
  obtain ⟨K, hK, hbound⟩ :=
    (Fintype.linearCombination ℝ v).injective_iff_antilipschitz.mp
      hv.fintypeLinearCombination_injective
  have hK' : 0 < (K : ℝ) := by exact_mod_cast hK
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr hK', fun c ↦ ?_⟩
  have h := hbound.le_mul_dist c 0
  simp only [dist_zero_right, map_zero, Fintype.linearCombination_apply] at h
  calc
    (K : ℝ)⁻¹ * ‖c‖ ≤ (K : ℝ)⁻¹ * ((K : ℝ) * ‖∑ i, c i • v i‖) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hK'.le)
    _ = ‖∑ i, c i • v i‖ := by field_simp

/-- A pointwise error bound on finite columns gives the actual operator bound
with the native supremum norm on the finite coefficient domain. -/
theorem norm_finite_column_error_le (e : Fin r → V) {b : ℝ} (_hb : 0 ≤ b)
    (he : ∀ i, ‖e i‖ ≤ b) (c : Fin r → ℝ) :
    ‖∑ i, c i • e i‖ ≤ (r : ℝ) * b * ‖c‖ := by
  calc
    ‖∑ i, c i • e i‖ ≤ ∑ i, ‖c i • e i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin r, ‖c‖ * b := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm c i) (he i) (norm_nonneg _) (norm_nonneg _)
    _ = (r : ℝ) * b * ‖c‖ := by simp; ring

/-- Actual columns in one linear-map image retain rank under a genuinely small
native norm perturbation of a fixed finite frame. The theorem proves an
injective map INTO that same image; desired rank is not an assumption.

The map `Q` is used below as the actual normal-subspace inclusion. No
injectivity or isometry hypothesis on `Q` is needed for this implication. -/
theorem finrank_range_ge_of_close_finite_columns [FiniteDimensional ℝ W]
    (L : P →L[ℝ] W) (Q : W →L[ℝ] V) (d : Fin r → P) (v : Fin r → V)
    {m b : ℝ} (hb : 0 ≤ b)
    (hframe : ∀ c : Fin r → ℝ, m * ‖c‖ ≤ ‖∑ i, c i • v i‖)
    (herror : ∀ i, ‖Q (L (d i)) - v i‖ ≤ b) (hsmall : (r : ℝ) * b < m) :
    r ≤ Module.finrank ℝ (LinearMap.range L.toLinearMap) := by
  let T := L.toLinearMap.comp (Fintype.linearCombination ℝ d)
  have hT : Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    have hsum : ∑ i, c i • Q (L (d i)) = 0 := by
      have h := congrArg Q hc
      change Q (L (∑ i, c i • d i)) = Q 0 at h
      simpa only [map_sum, map_smul, map_zero] using h
    have hnorm := norm_finite_column_error_le (fun i ↦ Q (L (d i)) - v i) hb herror c
    simp only [smul_sub, Finset.sum_sub_distrib, hsum, zero_sub, norm_neg] at hnorm
    have hc0 : ‖c‖ = 0 := by
      have hf := hframe c
      nlinarith [norm_nonneg c]
    exact norm_eq_zero.mp hc0
  let Tr : (Fin r → ℝ) →ₗ[ℝ] LinearMap.range L.toLinearMap :=
    T.codRestrict _ (fun c ↦ ⟨Fintype.linearCombination ℝ d c, rfl⟩)
  have hTr : Injective Tr := by
    intro c c' hcc
    exact hT (congrArg Subtype.val hcc)
  simpa only [Module.finrank_fin_fun] using LinearMap.finrank_le_finrank_of_injective hTr

end FiniteColumns

section RadialPair

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The literal radial direction in the SAME parameter space. No angle is
restricted, and the coefficients are always bounded in absolute value by one. -/
def pairedRadialDirection (theta : ℝ) (d0 d1 : P) : P :=
  Real.cos theta • d0 + Real.sin theta • d1

/-- Native linearity and `cos² + sin² = 1` remove all fast-angle dependence
from the leading response of the two actual parameter columns. -/
theorem pairedRadialDirection_response (L : P →L[ℝ] V)
    (theta a : ℝ) (d0 d1 : P) (v e0 e1 : V)
    (h0 : L d0 = (a * Real.cos theta) • v + e0)
    (h1 : L d1 = (a * Real.sin theta) • v + e1) :
    L (pairedRadialDirection theta d0 d1) =
      a • v + (Real.cos theta • e0 + Real.sin theta • e1) := by
  rw [pairedRadialDirection, map_add, map_smul, map_smul, h0, h1]
  calc
    _ = (a * (Real.cos theta ^ 2 + Real.sin theta ^ 2)) • v +
        (Real.cos theta • e0 + Real.sin theta • e1) := by module
    _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]

/-- Radial recombination of two endpoint differences costs at most four
remainder bounds, uniformly over ALL real fast angles. -/
theorem pairedRadialDirection_four_remainders_norm_le
    (theta : ℝ) (e0x e0y e1x e1y : V) {b : ℝ} (_hb : 0 ≤ b)
    (h0x : ‖e0x‖ ≤ b) (h0y : ‖e0y‖ ≤ b)
    (h1x : ‖e1x‖ ≤ b) (h1y : ‖e1y‖ ≤ b) :
    ‖Real.cos theta • (e0x - e0y) + Real.sin theta • (e1x - e1y)‖ ≤ 4 * b := by
  have h0 : ‖e0x - e0y‖ ≤ 2 * b := (norm_sub_le _ _).trans (by linarith)
  have h1 : ‖e1x - e1y‖ ≤ 2 * b := (norm_sub_le _ _).trans (by linarith)
  calc
    _ ≤ ‖Real.cos theta • (e0x - e0y)‖ + ‖Real.sin theta • (e1x - e1y)‖ :=
      norm_add_le _ _
    _ ≤ 1 * (2 * b) + 1 * (2 * b) := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact add_le_add
        (mul_le_mul (Real.abs_cos_le_one theta) h0 (norm_nonneg _) (by norm_num))
        (mul_le_mul (Real.abs_sin_le_one theta) h1 (norm_nonneg _) (by norm_num))
    _ = 4 * b := by ring

end RadialPair

section ActualCoincidenceColumns

variable {p N r : ℕ} {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The actual normal-projector discrepancy is controlled by the actual native
first-derivative discrepancy. This applies the ORIGINAL coercive-frame theorem
to the true differentials of the two maps, with no supplied projection map.
Source: the normal-bundle comparison underlying (8.1)–(8.2). -/
theorem actual_normal_projection_gap_of_derivative_close
    [FiniteDimensional ℝ E]
    [Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    (F G : M → EuclideanSpace ℝ (Fin N)) (x : M) {lam : ℝ} (hlam : 0 < lam)
    (hF : ∀ w : TangentSpace 𝓘(ℝ, E) x,
      lam * ‖w‖ ^ 2 ≤ ‖mvfderiv 𝓘(ℝ, E) F x w‖ ^ 2)
    (hclose : ‖mvfderiv 𝓘(ℝ, E) F x - mvfderiv 𝓘(ℝ, E) G x‖ ≤ Real.sqrt lam / 2) :
    ‖(normalSpace (I := 𝓘(ℝ, E)) G x).starProjection -
      (normalSpace (I := 𝓘(ℝ, E)) F x).starProjection‖ ≤
        (3 / Real.sqrt lam) * ‖mvfderiv 𝓘(ℝ, E) F x - mvfderiv 𝓘(ℝ, E) G x‖ := by
  have h := (pointwise_projected_jet_estimate
    (mvfderiv 𝓘(ℝ, E) F x) (mvfderiv 𝓘(ℝ, E) G x)
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N)))
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N))) lam 1
    hlam hF hclose ContinuousLinearMap.norm_id_le).2
  change ‖(LinearMap.range (mvfderiv 𝓘(ℝ, E) G x).toLinearMap)ᗮ.starProjection -
    (LinearMap.range (mvfderiv 𝓘(ℝ, E) F x).toLinearMap)ᗮ.starProjection‖ ≤ _
  simpa using h

/-- A fixed actual reference-normal leading vector remains close to its
projection onto the current map's actual normal space, with the explicit
native C¹ error factor. Thus `eta` need not be supplied independently. -/
theorem actual_normal_projection_vector_error_le
    [FiniteDimensional ℝ E]
    [Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    (F G : M → EuclideanSpace ℝ (Fin N)) (x : M) {lam : ℝ} (hlam : 0 < lam)
    (hF : ∀ w : TangentSpace 𝓘(ℝ, E) x,
      lam * ‖w‖ ^ 2 ≤ ‖mvfderiv 𝓘(ℝ, E) F x w‖ ^ 2)
    (hclose : ‖mvfderiv 𝓘(ℝ, E) F x - mvfderiv 𝓘(ℝ, E) G x‖ ≤ Real.sqrt lam / 2)
    (v : EuclideanSpace ℝ (Fin N)) (hv : v ∈ normalSpace (I := 𝓘(ℝ, E)) F x) :
    ‖(normalSpace (I := 𝓘(ℝ, E)) G x).starProjection v - v‖ ≤
      (3 / Real.sqrt lam) * ‖mvfderiv 𝓘(ℝ, E) F x - mvfderiv 𝓘(ℝ, E) G x‖ * ‖v‖ := by
  let Q := (normalSpace (I := 𝓘(ℝ, E)) G x).starProjection -
    (normalSpace (I := 𝓘(ℝ, E)) F x).starProjection
  have hQ : Q v = (normalSpace (I := 𝓘(ℝ, E)) G x).starProjection v - v := by
    simp only [Q, sub_apply, Submodule.starProjection_eq_self_iff.mpr hv]
  rw [← hQ]
  exact (Q.le_opNorm v).trans (mul_le_mul_of_nonneg_right
    (actual_normal_projection_gap_of_derivative_close F G x hlam hF hclose) (norm_nonneg v))

/-- The actual normal derivative of the value DIFFERENCE, on the radial
parameter direction, has the phase-independent leading response and BOTH
endpoint remainders. The formulas at the two points are native derivatives of
the SAME actual family; only the leading terms at `y` vanish.

The leading ambient vector need not lie in the varying normal space. Its
actual projection is kept explicitly, so the normal-bundle comparison error
cannot silently disappear. -/
theorem actual_coincidence_paired_radial_response
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (u : Fin p → ℝ) (x y : M) (theta a : ℝ)
    (d0 d1 : Fin p → ℝ) (v e0x e0y e1x e1y : EuclideanSpace ℝ (Fin N))
    (hx : DifferentiableAt ℝ (fun w ↦ G w x) u)
    (hy : DifferentiableAt ℝ (fun w ↦ G w y) u)
    (h0x : fderiv ℝ (fun w ↦ G w x) u d0 = (a * Real.cos theta) • v + e0x)
    (h0y : fderiv ℝ (fun w ↦ G w y) u d0 = e0y)
    (h1x : fderiv ℝ (fun w ↦ G w x) u d1 = (a * Real.sin theta) • v + e1x)
    (h1y : fderiv ℝ (fun w ↦ G w y) u d1 = e1y) :
    ((coincidenceParameterNormalDerivative (E := E) G u x y)
        (pairedRadialDirection theta d0 d1) : EuclideanSpace ℝ (Fin N)) =
      a • (normalSpace (I := 𝓘(ℝ, E)) (G u) x).starProjection v +
        (normalSpace (I := 𝓘(ℝ, E)) (G u) x).starProjection
          (Real.cos theta • (e0x - e0y) + Real.sin theta • (e1x - e1y)) := by
  let D := fderiv ℝ (fun w ↦ G w x - G w y) u
  have h0 : D d0 = (a * Real.cos theta) • v + (e0x - e0y) := by
    change fderiv ℝ ((fun w ↦ G w x) - fun w ↦ G w y) u d0 = _
    rw [fderiv_sub hx hy, sub_apply, h0x, h0y]
    module
  have h1 : D d1 = (a * Real.sin theta) • v + (e1x - e1y) := by
    change fderiv ℝ ((fun w ↦ G w x) - fun w ↦ G w y) u d1 = _
    rw [fderiv_sub hx hy, sub_apply, h1x, h1y]
    module
  have hresponse := pairedRadialDirection_response D theta a d0 d1 v
    (e0x - e0y) (e1x - e1y) h0 h1
  change (normalSpace (I := 𝓘(ℝ, E)) (G u) x).starProjection
    (D (pairedRadialDirection theta d0 d1)) = _
  rw [hresponse, map_add, map_smul]

/-- One actual radial difference column is within `a*(eta + 4*eps)` of the
fixed leading value vector. `eta` is the REAL current-normal projection error;
the factor four accounts for both sine/cosine columns at both source points.
The bound is uniform over all fast angles. -/
theorem actual_coincidence_paired_radial_error_le
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (u : Fin p → ℝ) (x y : M) (theta : ℝ) {a eta eps : ℝ}
    (ha : 0 ≤ a) (heps : 0 ≤ eps)
    (d0 d1 : Fin p → ℝ) (v e0x e0y e1x e1y : EuclideanSpace ℝ (Fin N))
    (hx : DifferentiableAt ℝ (fun w ↦ G w x) u)
    (hy : DifferentiableAt ℝ (fun w ↦ G w y) u)
    (h0x : fderiv ℝ (fun w ↦ G w x) u d0 = (a * Real.cos theta) • v + e0x)
    (h0y : fderiv ℝ (fun w ↦ G w y) u d0 = e0y)
    (h1x : fderiv ℝ (fun w ↦ G w x) u d1 = (a * Real.sin theta) • v + e1x)
    (h1y : fderiv ℝ (fun w ↦ G w y) u d1 = e1y)
    (hproj : ‖(normalSpace (I := 𝓘(ℝ, E)) (G u) x).starProjection v - v‖ ≤ eta)
    (hR0x : ‖e0x‖ ≤ a * eps) (hR0y : ‖e0y‖ ≤ a * eps)
    (hR1x : ‖e1x‖ ≤ a * eps) (hR1y : ‖e1y‖ ≤ a * eps) :
    ‖((coincidenceParameterNormalDerivative (E := E) G u x y)
        (pairedRadialDirection theta d0 d1) : EuclideanSpace ℝ (Fin N)) - a • v‖ ≤
      a * (eta + 4 * eps) := by
  rw [actual_coincidence_paired_radial_response G u x y theta a d0 d1 v
    e0x e0y e1x e1y hx hy h0x h0y h1x h1y]
  let Q := (normalSpace (I := 𝓘(ℝ, E)) (G u) x).starProjection
  let e := Real.cos theta • (e0x - e0y) + Real.sin theta • (e1x - e1y)
  change ‖a • Q v + Q e - a • v‖ ≤ _
  have he := pairedRadialDirection_four_remainders_norm_le theta e0x e0y e1x e1y
    (mul_nonneg ha heps) hR0x hR0y hR1x hR1y
  have hrewrite : a • Q v + Q e - a • v = a • (Q v - v) + Q e := by module
  rw [hrewrite]
  calc
    _ ≤ ‖a • (Q v - v)‖ + ‖Q e‖ := norm_add_le _ _
    _ ≤ a * eta + 4 * (a * eps) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      exact add_le_add (mul_le_mul_of_nonneg_left hproj ha)
        (((normalSpace (I := 𝓘(ℝ, E)) (G u) x).norm_starProjection_apply_le e).trans he)
    _ = a * (eta + 4 * eps) := by ring

/-- The source's paired value responses, including actual GLOBAL remainders
at both endpoints and the true current-normal projection discrepancy, force
rank at least `r` for the SAME actual normal parameter derivative.

All dependence on fast angles is absent from the smallness condition
`r*(eta+4*eps) < m`. The supplied finite frame is a fixed leading frame with a
positive lower norm margin; the genuine probe construction and normal-bundle
comparison must supply the displayed response and error estimates. -/
theorem coincidence_parameter_normal_rank_of_paired_responses
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (u : Fin p → ℝ) (x y : M)
    {a m eta eps : ℝ} (ha : 0 < a) (heta : 0 ≤ eta) (heps : 0 ≤ eps)
    (theta : Fin r → ℝ) (d0 d1 : Fin r → Fin p → ℝ)
    (v e0x e0y e1x e1y : Fin r → EuclideanSpace ℝ (Fin N))
    (hx : DifferentiableAt ℝ (fun w ↦ G w x) u)
    (hy : DifferentiableAt ℝ (fun w ↦ G w y) u)
    (hframe : ∀ c : Fin r → ℝ, m * ‖c‖ ≤ ‖∑ i, c i • v i‖)
    (h0x : ∀ i, fderiv ℝ (fun w ↦ G w x) u (d0 i) =
      (a * Real.cos (theta i)) • v i + e0x i)
    (h0y : ∀ i, fderiv ℝ (fun w ↦ G w y) u (d0 i) = e0y i)
    (h1x : ∀ i, fderiv ℝ (fun w ↦ G w x) u (d1 i) =
      (a * Real.sin (theta i)) • v i + e1x i)
    (h1y : ∀ i, fderiv ℝ (fun w ↦ G w y) u (d1 i) = e1y i)
    (hproj : ∀ i, ‖(normalSpace (I := 𝓘(ℝ, E)) (G u) x).starProjection (v i) - v i‖ ≤ eta)
    (hR0x : ∀ i, ‖e0x i‖ ≤ a * eps) (hR0y : ∀ i, ‖e0y i‖ ≤ a * eps)
    (hR1x : ∀ i, ‖e1x i‖ ≤ a * eps) (hR1y : ∀ i, ‖e1y i‖ ≤ a * eps)
    (hsmall : (r : ℝ) * (eta + 4 * eps) < m) :
    r ≤ Module.finrank ℝ (LinearMap.range
      (coincidenceParameterNormalDerivative (E := E) G u x y).toLinearMap) := by
  apply finrank_range_ge_of_close_finite_columns
    (coincidenceParameterNormalDerivative (E := E) G u x y)
    (normalSpace (I := 𝓘(ℝ, E)) (G u) x).subtypeL
    (fun i ↦ pairedRadialDirection (theta i) (d0 i) (d1 i)) (fun i ↦ a • v i)
    (m := a * m) (b := a * (eta + 4 * eps)) (by positivity)
  · intro c
    have hsum : (∑ i, c i • a • v i) = a • ∑ i, c i • v i := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      exact smul_comm _ _ _
    rw [hsum, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    nlinarith [hframe c]
  · intro i
    exact actual_coincidence_paired_radial_error_le G u x y (theta i) ha.le heps
      (d0 i) (d1 i) (v i) (e0x i) (e0y i) (e1x i) (e1y i) hx hy
      (h0x i) (h0y i) (h1x i) (h1y i) (hproj i)
      (hR0x i) (hR0y i) (hR1x i) (hR1y i)
  · nlinarith [mul_lt_mul_of_pos_left hsmall ha]

/-- A fixed independent leading frame has ONE positive response tolerance,
chosen before the actual family, amplitude, parameter, source pair, directions,
or arbitrary fast angles. The leading frame can include the source's fixed
nonzero weights `-lambda⁻²` and plateau cutoff values.

The actual current-normal projection and all four global remainder columns
must obey this tolerance; neither rank nor independence of the actual columns
is assumed. This is the uniform fast-angle stability assertion used on each
member of the finite wave cover. -/
theorem exists_uniform_paired_value_rank_tolerance
    (v : Fin r → EuclideanSpace ℝ (Fin N)) (hv : LinearIndependent ℝ v) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ (p : ℕ) (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
        (u : Fin p → ℝ) (x y : M) (a : ℝ), 0 < a →
        ∀ (theta : Fin r → ℝ) (d0 d1 : Fin r → Fin p → ℝ)
          (e0x e0y e1x e1y : Fin r → EuclideanSpace ℝ (Fin N)),
        DifferentiableAt ℝ (fun w ↦ G w x) u →
        DifferentiableAt ℝ (fun w ↦ G w y) u →
        (∀ i, fderiv ℝ (fun w ↦ G w x) u (d0 i) =
          (a * Real.cos (theta i)) • v i + e0x i) →
        (∀ i, fderiv ℝ (fun w ↦ G w y) u (d0 i) = e0y i) →
        (∀ i, fderiv ℝ (fun w ↦ G w x) u (d1 i) =
          (a * Real.sin (theta i)) • v i + e1x i) →
        (∀ i, fderiv ℝ (fun w ↦ G w y) u (d1 i) = e1y i) →
        (∀ i, ‖(normalSpace (I := 𝓘(ℝ, E)) (G u) x).starProjection (v i) - v i‖ ≤ eps) →
        (∀ i, ‖e0x i‖ ≤ a * eps) → (∀ i, ‖e0y i‖ ≤ a * eps) →
        (∀ i, ‖e1x i‖ ≤ a * eps) → (∀ i, ‖e1y i‖ ≤ a * eps) →
        r ≤ Module.finrank ℝ (LinearMap.range
          (coincidenceParameterNormalDerivative (E := E) G u x y).toLinearMap) := by
  obtain ⟨m, hm, hframe⟩ := exists_positive_finite_frame_margin v hv
  let eps := m / (10 * ((r : ℝ) + 1))
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hidentity : (10 * ((r : ℝ) + 1)) * eps = m := by
    dsimp [eps]
    field_simp
  have hsmall : (r : ℝ) * (eps + 4 * eps) < m := by nlinarith
  refine ⟨eps, heps, ?_⟩
  intro p G u x y a ha theta d0 d1 e0x e0y e1x e1y hx hy
    h0x h0y h1x h1y hproj hR0x hR0y hR1x hR1y
  exact coincidence_parameter_normal_rank_of_paired_responses G u x y ha heps.le heps.le
    theta d0 d1 v e0x e0y e1x e1y hx hy hframe h0x h0y h1x h1y hproj
    hR0x hR0y hR1x hR1y hsmall

/-- The full local paired-value rank consumer uses a FIXED reference immersion
and independent reference-normal vectors. One C¹ tolerance and one normalized
remainder tolerance are fixed before the parameter dimension, actual family,
amplitude, second source point, and all fast angles.

The current-normal projection bounds are PROVED from the real first-derivative
closeness, using the original Riemannian tangent norms and original projection
stability theorem. The only geometric provider still required here is the real
paired response formula with its global remainders at both points. -/
theorem exists_paired_value_rank_tolerances_of_reference_frame
    [FiniteDimensional ℝ E]
    [Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    (F : M → EuclideanSpace ℝ (Fin N)) (x : M) {lam : ℝ} (hlam : 0 < lam)
    (hF : ∀ w : TangentSpace 𝓘(ℝ, E) x,
      lam * ‖w‖ ^ 2 ≤ ‖mvfderiv 𝓘(ℝ, E) F x w‖ ^ 2)
    (v : Fin r → EuclideanSpace ℝ (Fin N)) (hv : LinearIndependent ℝ v)
    (hnormal : ∀ i, v i ∈ normalSpace (I := 𝓘(ℝ, E)) F x) :
    ∃ eps delta : ℝ, 0 < eps ∧ 0 < delta ∧
      ∀ (p : ℕ) (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
        (u : Fin p → ℝ) (y : M) (a : ℝ), 0 < a →
        ∀ (theta : Fin r → ℝ) (d0 d1 : Fin r → Fin p → ℝ)
          (e0x e0y e1x e1y : Fin r → EuclideanSpace ℝ (Fin N)),
        DifferentiableAt ℝ (fun w ↦ G w x) u →
        DifferentiableAt ℝ (fun w ↦ G w y) u →
        ‖mvfderiv 𝓘(ℝ, E) F x - mvfderiv 𝓘(ℝ, E) (G u) x‖ ≤ delta →
        (∀ i, fderiv ℝ (fun w ↦ G w x) u (d0 i) =
          (a * Real.cos (theta i)) • v i + e0x i) →
        (∀ i, fderiv ℝ (fun w ↦ G w y) u (d0 i) = e0y i) →
        (∀ i, fderiv ℝ (fun w ↦ G w x) u (d1 i) =
          (a * Real.sin (theta i)) • v i + e1x i) →
        (∀ i, fderiv ℝ (fun w ↦ G w y) u (d1 i) = e1y i) →
        (∀ i, ‖e0x i‖ ≤ a * eps) → (∀ i, ‖e0y i‖ ≤ a * eps) →
        (∀ i, ‖e1x i‖ ≤ a * eps) → (∀ i, ‖e1y i‖ ≤ a * eps) →
        r ≤ Module.finrank ℝ (LinearMap.range
          (coincidenceParameterNormalDerivative (E := E) G u x y).toLinearMap) := by
  obtain ⟨eps, heps, hrank⟩ := exists_uniform_paired_value_rank_tolerance (E := E) (M := M) v hv
  let R : ℝ := 1 + ∑ i, ‖v i‖
  have hR : 0 < R := by dsimp [R]; positivity
  have hRv (i : Fin r) : ‖v i‖ ≤ R := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) ↦ norm_nonneg (v j))
      (Finset.mem_univ i)
    dsimp [R]
    linarith
  let C : ℝ := 3 / Real.sqrt lam
  have hC : 0 < C := by dsimp [C]; positivity
  let delta := min (Real.sqrt lam / 2) (eps / (C * R))
  have hdelta : 0 < delta := lt_min (by positivity) (div_pos heps (mul_pos hC hR))
  have hdeltaSmall : delta ≤ Real.sqrt lam / 2 := min_le_left _ _
  have hdeltaBudget : C * delta * R ≤ eps := by
    have h := (le_div_iff₀ (mul_pos hC hR)).mp (min_le_right
      (Real.sqrt lam / 2) (eps / (C * R)))
    nlinarith
  refine ⟨eps, delta, heps, hdelta, ?_⟩
  intro p G u y a ha theta d0 d1 e0x e0y e1x e1y hx hy hclose
    h0x h0y h1x h1y hR0x hR0y hR1x hR1y
  apply hrank p G u x y a ha theta d0 d1 e0x e0y e1x e1y hx hy
    h0x h0y h1x h1y
  · intro i
    have h := actual_normal_projection_vector_error_le F (G u) x hlam hF
      (hclose.trans hdeltaSmall) (v i) (hnormal i)
    apply h.trans
    change C * ‖mvfderiv 𝓘(ℝ, E) F x - mvfderiv 𝓘(ℝ, E) (G u) x‖ * ‖v i‖ ≤ eps
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hclose hC.le) (hRv i)
      (norm_nonneg _) (mul_nonneg hC.le hdelta.le)).trans hdeltaBudget
  · exact hR0x
  · exact hR0y
  · exact hR1x
  · exact hR1y

local instance pairedValueRankPairChartedSpace : ChartedSpace (E × E) (M × M) :=
  prodChartedSpace E M E M

/-- The genuine paired responses now imply the rank of the ACTUAL joint
coincidence derivative, adding the actual source tangent dimension. Joint
smoothness proves the parameter-slice differentiability hypotheses.

For `r = dim M + 1`, this is exactly rank `2 dim M + 1`, the threshold consumed
by the original finite-parameter avoidance theorem. The actual global family
construction and its response estimates remain upstream. -/
theorem coincidence_joint_rank_of_paired_value_responses
    [FiniteDimensional ℝ E]
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (Pdom : Set (Fin p → ℝ)) (hPdom : IsOpen Pdom)
    (hG : ContMDiffOn ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (Function.uncurry G) (Pdom ×ˢ Set.univ))
    (u : Fin p → ℝ) (hu : u ∈ Pdom) (x y : M)
    (himm : Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (G u) x))
    {a m eta eps : ℝ} (ha : 0 < a) (heta : 0 ≤ eta) (heps : 0 ≤ eps)
    (theta : Fin r → ℝ) (d0 d1 : Fin r → Fin p → ℝ)
    (v e0x e0y e1x e1y : Fin r → EuclideanSpace ℝ (Fin N))
    (hframe : ∀ c : Fin r → ℝ, m * ‖c‖ ≤ ‖∑ i, c i • v i‖)
    (h0x : ∀ i, fderiv ℝ (fun w ↦ G w x) u (d0 i) =
      (a * Real.cos (theta i)) • v i + e0x i)
    (h0y : ∀ i, fderiv ℝ (fun w ↦ G w y) u (d0 i) = e0y i)
    (h1x : ∀ i, fderiv ℝ (fun w ↦ G w x) u (d1 i) =
      (a * Real.sin (theta i)) • v i + e1x i)
    (h1y : ∀ i, fderiv ℝ (fun w ↦ G w y) u (d1 i) = e1y i)
    (hproj : ∀ i, ‖(normalSpace (I := 𝓘(ℝ, E)) (G u) x).starProjection (v i) - v i‖ ≤ eta)
    (hR0x : ∀ i, ‖e0x i‖ ≤ a * eps) (hR0y : ∀ i, ‖e0y i‖ ≤ a * eps)
    (hR1x : ∀ i, ‖e1x i‖ ≤ a * eps) (hR1y : ∀ i, ‖e1y i‖ ≤ a * eps)
    (hsmall : (r : ℝ) * (eta + 4 * eps) < m) :
    Module.finrank ℝ E + r ≤ Module.finrank ℝ (LinearMap.range
      (mfderiv ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, Fin N → ℝ)
        (euclideanCoincidenceMap G) (u, x, y)).toLinearMap) := by
  have hparam (z : M) : DifferentiableAt ℝ (fun w ↦ G w z) u :=
    (((hG.contMDiffAt ((hPdom.prod isOpen_univ).mem_nhds ⟨hu, Set.mem_univ z⟩)).curry_left
      ).contDiffAt).differentiableAt (by simp)
  exact coincidence_joint_rank_of_parameter_normal_rank G Pdom hPdom hG u hu x y himm r
    (coincidence_parameter_normal_rank_of_paired_responses G u x y ha heta heps
      theta d0 d1 v e0x e0y e1x e1y (hparam x) (hparam y) hframe
      h0x h0y h1x h1y hproj hR0x hR0y hR1x hR1y hsmall)

end ActualCoincidenceColumns

#print axioms exists_positive_finite_frame_margin
#print axioms norm_finite_column_error_le
#print axioms finrank_range_ge_of_close_finite_columns
#print axioms pairedRadialDirection_response
#print axioms pairedRadialDirection_four_remainders_norm_le
#print axioms actual_normal_projection_gap_of_derivative_close
#print axioms actual_normal_projection_vector_error_le
#print axioms actual_coincidence_paired_radial_response
#print axioms actual_coincidence_paired_radial_error_le
#print axioms coincidence_parameter_normal_rank_of_paired_responses
#print axioms exists_uniform_paired_value_rank_tolerance
#print axioms exists_paired_value_rank_tolerances_of_reference_frame
#print axioms coincidence_joint_rank_of_paired_value_responses

end GlobalEmbedding.Offline
