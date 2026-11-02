import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Algebra.Support

/-!
# Actual fixed-profile scaled chart bumps

Source: `literature/parallelizable-stable-plus-one/main.tex`, the colored-cutoff
construction in `prop:initialization`, and original node
`initialization-colored-cutoffs-square-partition-scaled-bumps`.

The profile is one fixed native `ContDiffBump` with inner radius one and outer
radius `3/2`. The actual scaled function is `eta ((10*K/rho) • y)`. Its entire
iterated Fréchet derivative is computed by the native linear chain rule, giving
the full uniform `B_j*K^j` bound. The manifold function is the literal chart
pullback extended by zero; no uniform exponential-chart existence is assumed to
have been proved. A genuine smooth chart and its radius buffer are explicit inputs.

This is an isolated offline candidate, not a main-library acceptance receipt.
-/

noncomputable section

open Function Filter Manifold IsManifold Set Metric
open scoped Topology ContDiff

namespace GlobalEmbedding.Offline

section EuclideanProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The one fixed native smooth profile for all centers and all scales.
Source: the original scaled-bumps node, inner radius `1`, outer radius `3/2`. -/
def unitCutoffProfile : ContDiffBump (0 : E) :=
  ⟨1, 3 / 2, by norm_num, by norm_num⟩

/-- The literal profile under the scalar dilation prescribed in the source. -/
def scaledCutoffProfile (rho K : ℝ) : E → ℝ :=
  fun y ↦ unitCutoffProfile (E := E) ((10 * K / rho) • y)

/-- The actual scaled profile is smooth at all orders by smooth linear
composition. No positivity is needed for this smoothness statement.
Source: the original scaled-bumps node. -/
theorem scaledCutoffProfile_contDiff (rho K : ℝ) :
    ContDiff ℝ ∞ (scaledCutoffProfile (E := E) rho K) := by
  have hscale : ContDiff ℝ ∞ (fun y : E ↦ (10 * K / rho) • y) :=
    contDiff_const.smul contDiff_id
  exact (unitCutoffProfile (E := E)).contDiff.comp hscale

/-- The original native profile has values in `[0,1]`, after any dilation.
Source: the original scaled-bumps node. -/
theorem scaledCutoffProfile_mem_Icc (rho K : ℝ) (y : E) :
    scaledCutoffProfile rho K y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(unitCutoffProfile (E := E)).nonneg, (unitCutoffProfile (E := E)).le_one⟩

/-- Exact plateau radius of the actual scaled profile.
Proof: the dilation sends this closed ball into the native unit plateau.
Source: radius `rho/(10*K)` in the original scaled-bumps node. -/
theorem scaledCutoffProfile_one
    (rho K : ℝ) (hrho : 0 < rho) (hK : 1 ≤ K)
    {y : E} (hy : y ∈ Metric.closedBall 0 (rho / (10 * K))) :
    scaledCutoffProfile rho K y = 1 := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have ha : 0 < 10 * K / rho := by positivity
  apply (unitCutoffProfile (E := E)).one_of_mem_closedBall
  change dist ((10 * K / rho) • y) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  have hy' : ‖y‖ ≤ rho / (10 * K) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  calc
    (10 * K / rho) * ‖y‖ ≤ (10 * K / rho) * (rho / (10 * K)) :=
      mul_le_mul_of_nonneg_left hy' ha.le
    _ = 1 := by field_simp

/-- Exact ordinary support of the actual scaled profile. This keeps the true
outer radius `3*rho/(20*K)`; the larger source radii are only buffers.
Proof: pull back the native outer ball by the positive scalar dilation.
Source: the original scaled-bumps node. -/
theorem scaledCutoffProfile_support
    (rho K : ℝ) (hrho : 0 < rho) (hK : 1 ≤ K) :
    Function.support (scaledCutoffProfile (E := E) rho K) =
      Metric.ball 0 (3 * rho / (20 * K)) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have ha : 0 < 10 * K / rho := by positivity
  change Function.support ((unitCutoffProfile (E := E) : E → ℝ) ∘
    (fun y ↦ (10 * K / rho) • y)) = _
  rw [Function.support_comp_eq_preimage, ContDiffBump.support_eq]
  ext y
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos ha]
  change (10 * K / rho) * ‖y‖ < (3 / 2 : ℝ) ↔ ‖y‖ < 3 * rho / (20 * K)
  have hradius : (10 * K / rho) * (3 * rho / (20 * K)) = (3 / 2 : ℝ) := by
    field_simp
    ring
  rw [← hradius, mul_lt_mul_iff_right₀ ha]

/-- Exact closed topological support and compactness, including the
zero-dimensional model. Proof: close the preceding positive-radius ball and use
native finite-dimensional closed-ball compactness.
Source: the original scaled-bumps node. -/
theorem scaledCutoffProfile_tsupport
    (rho K : ℝ) (hrho : 0 < rho) (hK : 1 ≤ K) :
    tsupport (scaledCutoffProfile (E := E) rho K) = Metric.closedBall 0 (3 * rho / (20 * K)) ∧
      HasCompactSupport (scaledCutoffProfile (E := E) rho K) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hr : 0 < 3 * rho / (20 * K) := by positivity
  have ht : tsupport (scaledCutoffProfile (E := E) rho K) =
      Metric.closedBall 0 (3 * rho / (20 * K)) := by
    rw [tsupport, scaledCutoffProfile_support rho K hrho hK, closure_ball _ hr.ne']
  exact ⟨ht, by simpa only [HasCompactSupport, ht] using isCompact_closedBall (0 : E) _⟩

/-- The entire actual order-`j` derivative scales by the exact factor
`(10*K/rho)^j`; this is an equality of native continuous multilinear maps.

Proof: invoke the existing iterated-derivative rule for composition with the
continuous linear map `(10*K/rho) • id`, then use multilinearity in all `j`
arguments. Order zero and the zero-dimensional model require no exception.
Source: the chain-rule calculation of the original scaled-bumps node. -/
theorem iteratedFDeriv_scaledCutoffProfile
    (rho K : ℝ) (j : ℕ) (y : E) :
    iteratedFDeriv ℝ j (scaledCutoffProfile (E := E) rho K) y =
      (10 * K / rho) ^ j •
        iteratedFDeriv ℝ j (unitCutoffProfile (E := E)) ((10 * K / rho) • y) := by
  let L : E →L[ℝ] E := (10 * K / rho) • ContinuousLinearMap.id ℝ E
  have heta : ContDiff ℝ ∞ (unitCutoffProfile (E := E)) :=
    (unitCutoffProfile (E := E)).contDiff
  have h := L.iteratedFDeriv_comp_right heta y (i := j) (by simp)
  change iteratedFDeriv ℝ j ((unitCutoffProfile (E := E) : E → ℝ) ∘ L) y = _
  rw [h]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply]
  change (iteratedFDeriv ℝ j (unitCutoffProfile (E := E)) ((10 * K / rho) • y))
      (fun i ↦ (10 * K / rho) • v i) = _
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ j (unitCutoffProfile (E := E)) ((10 * K / rho) • y)).map_smul_univ
      (fun _ : Fin j ↦ 10 * K / rho) v

/-- One sequence of finite constants bounds ALL actual derivatives of ALL scales
of the one fixed profile. `B j` depends only on the model, `rho`, and that profile;
it is quantified before `K` and contains no center or chart index.

Proof: use native compact-support derivative boundedness once for every order,
then the exact preceding linear-dilation formula. The constant is literally
`(10/rho)^j` times a fixed bound on `D^j eta`.
Source: `B_j K^j` in the original scaled-bumps node. -/
theorem exists_scaledCutoffProfile_derivative_bounds
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (K : ℝ), 1 ≤ K → ∀ (j : ℕ) (y : E),
        ‖iteratedFDeriv ℝ j (scaledCutoffProfile (E := E) rho K) y‖ ≤ B j * K ^ j := by
  choose C hCnonneg hC using fun j ↦
    (unitCutoffProfile (E := E)).hasCompactSupport.exists_bound_iteratedFDeriv
      (unitCutoffProfile (E := E)).contDiff j
  refine ⟨fun j ↦ (10 / rho) ^ j * C j, fun j ↦ mul_nonneg (by positivity) (hCnonneg j), ?_⟩
  intro K hK j y
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have ha : 0 ≤ (10 * K / rho) ^ j := by positivity
  rw [iteratedFDeriv_scaledCutoffProfile, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    (10 * K / rho) ^ j *
        ‖iteratedFDeriv ℝ j (unitCutoffProfile (E := E)) ((10 * K / rho) • y)‖ ≤
      (10 * K / rho) ^ j * C j := mul_le_mul_of_nonneg_left (hC j j le_rfl _) ha
    _ = (10 / rho) ^ j * C j * K ^ j := by
      rw [show 10 * K / rho = (10 / rho) * K by ring, mul_pow]
      ring

/-- All source radii are strictly nested, and the enlarged ball fits in the
given radius-`rho` chart buffer for `K≥1`. Proof: elementary inequalities using
positive `rho` and `K`, with the exact source constants.
Source: the original scaled-bumps node. -/
theorem scaledCutoffProfile_radius_nesting
    (rho K : ℝ) (hrho : 0 < rho) (hK : 1 ≤ K) :
    3 * rho / (20 * K) < rho / (5 * K) ∧
      rho / (5 * K) < rho / (4 * K) ∧ rho / (4 * K) < rho := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hprod : 0 < rho * K := mul_pos hrho hKpos
  constructor
  · apply (div_lt_div_iff₀ (by positivity : 0 < 20 * K) (by positivity : 0 < 5 * K)).mpr
    nlinarith
  constructor
  · apply (div_lt_div_iff₀ (by positivity : 0 < 5 * K) (by positivity : 0 < 4 * K)).mpr
    nlinarith
  · apply (div_lt_iff₀ (by positivity : 0 < 4 * K)).mpr
    nlinarith

end EuclideanProfile

section ChartPullback

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M]

/-- The actual chart pullback, set equal to zero off the original chart source.
This preserves the given normal chart and uses no replacement atlas. -/
def scaledChartCutoff (rho K : ℝ) (e : OpenPartialHomeomorph M E) : M → ℝ :=
  e.source.indicator (scaledCutoffProfile (E := E) rho K ∘ e)

/-- On the chart source, the zero extension is the prescribed literal profile.
Source: `b_p(exp_p y)=eta(10*K*y/rho)` in the scaled-bumps node. -/
theorem scaledChartCutoff_on_source (rho K : ℝ) (e : OpenPartialHomeomorph M E)
    {x : M} (hx : x ∈ e.source) :
    scaledChartCutoff rho K e x = scaledCutoffProfile rho K (e x) := by
  exact Set.indicator_of_mem hx _

/-- Off the original chart source the actual cutoff is exactly zero.
Source: the zero extension in the scaled-bumps node. -/
theorem scaledChartCutoff_off_source (rho K : ℝ) (e : OpenPartialHomeomorph M E)
    {x : M} (hx : x ∉ e.source) : scaledChartCutoff rho K e x = 0 := by
  exact Set.indicator_of_notMem hx _

/-- The same zero-extended cutoff takes values in `[0,1]` everywhere.
Source: the scaled-bumps node. -/
theorem scaledChartCutoff_mem_Icc (rho K : ℝ) (e : OpenPartialHomeomorph M E) (x : M) :
    scaledChartCutoff rho K e x ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hx : x ∈ e.source
  · rw [scaledChartCutoff_on_source rho K e hx]
    exact scaledCutoffProfile_mem_Icc rho K (e x)
  · rw [scaledChartCutoff_off_source rho K e hx]
    exact ⟨le_refl _, zero_le_one⟩

/-- The actual manifold plateau is the closed normal-coordinate ball with the
exact radius `rho/(10*K)`. Source: the scaled-bumps node. -/
theorem scaledChartCutoff_one (rho K : ℝ) (hrho : 0 < rho) (hK : 1 ≤ K)
    (e : OpenPartialHomeomorph M E) {x : M}
    (hx : x ∈ e.source ∩ e ⁻¹' Metric.closedBall 0 (rho / (10 * K))) :
    scaledChartCutoff rho K e x = 1 := by
  rw [scaledChartCutoff_on_source rho K e hx.1]
  exact scaledCutoffProfile_one rho K hrho hK hx.2

/-- Compact containment of the actual zero-extended support in the two prescribed
normal-coordinate buffers, with the sharper closed `3*rho/(20*K)` bound retained.

Proof: its ordinary support pulls back the exact scaled-profile support. The
closed outer ball lies in the supplied genuine chart target. Its inverse-chart
image is compact, hence closed in the original Hausdorff source and contains the
topological support. The exact strict radius inequalities give both buffers.
Source: the original scaled-bumps node. No exponential-chart existence is claimed.
-/
theorem scaledChartCutoff_support_buffers
    [T2Space M] (rho K : ℝ) (hrho : 0 < rho) (hK : 1 ≤ K)
    (e : OpenPartialHomeomorph M E)
    (hbuffer : Metric.closedBall (0 : E) rho ⊆ e.target) :
    tsupport (scaledChartCutoff rho K e) ⊆ e.symm '' Metric.closedBall 0 (3 * rho / (20 * K)) ∧
      HasCompactSupport (scaledChartCutoff rho K e) ∧
      tsupport (scaledChartCutoff rho K e) ⊆
        e.source ∩ e ⁻¹' Metric.ball 0 (rho / (5 * K)) ∧
      tsupport (scaledChartCutoff rho K e) ⊆
        e.source ∩ e ⁻¹' Metric.ball 0 (rho / (4 * K)) := by
  have hradii := scaledCutoffProfile_radius_nesting rho K hrho hK
  have houter : 3 * rho / (20 * K) < rho := hradii.1.trans (hradii.2.1.trans hradii.2.2)
  have htarget : Metric.closedBall (0 : E) (3 * rho / (20 * K)) ⊆ e.target :=
    (Metric.closedBall_subset_closedBall houter.le).trans hbuffer
  have hcompact : IsCompact (e.symm '' Metric.closedBall (0 : E) (3 * rho / (20 * K))) :=
    (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono htarget)
  have hsupp : Function.support (scaledChartCutoff rho K e) =
      e.source ∩ e ⁻¹' Metric.ball 0 (3 * rho / (20 * K)) := by
    rw [scaledChartCutoff, support_indicator, Function.support_comp_eq_preimage,
      scaledCutoffProfile_support rho K hrho hK]
  have hsub : Function.support (scaledChartCutoff rho K e) ⊆
      e.symm '' Metric.closedBall 0 (3 * rho / (20 * K)) := by
    intro x hx
    rw [hsupp] at hx
    exact ⟨e x, Metric.ball_subset_closedBall hx.2, e.left_inv hx.1⟩
  have htsub : tsupport (scaledChartCutoff rho K e) ⊆
      e.symm '' Metric.closedBall 0 (3 * rho / (20 * K)) :=
    closure_minimal hsub hcompact.isClosed
  have hsmall : tsupport (scaledChartCutoff rho K e) ⊆
      e.source ∩ e ⁻¹' Metric.ball 0 (rho / (5 * K)) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := htsub hx
    refine ⟨e.map_target (htarget hy), ?_⟩
    change e (e.symm y) ∈ Metric.ball 0 (rho / (5 * K))
    rw [e.right_inv (htarget hy)]
    exact (Metric.closedBall_subset_ball hradii.1) hy
  refine ⟨htsub, hcompact.of_isClosed_subset (isClosed_tsupport _) htsub, hsmall, ?_⟩
  intro x hx
  exact ⟨(hsmall hx).1, Metric.ball_subset_ball hradii.2.1.le (hsmall hx).2⟩

/-- The actual coordinate representative of the zero extension agrees with the
same scaled profile everywhere in the given chart target. No off-target junk
values of the partial inverse are constrained.
Source: the original scaled-bumps node. -/
theorem scaledChartCutoff_chart_eq
    (rho K : ℝ) (e : OpenPartialHomeomorph M E) {y : E} (hy : y ∈ e.target) :
    scaledChartCutoff rho K e (e.symm y) = scaledCutoffProfile rho K y := by
  rw [scaledChartCutoff_on_source rho K e (e.map_target hy), e.right_inv hy]

/-- All derivatives of the actual coordinate representative agree with those of
the one scaled profile on the OPEN target. This proves the genuine coordinate
derivative interface after zero extension.
Proof: the preceding equality holds in a neighborhood, so use the existing
iterated derivative germ theorem. Source: the scaled-bumps node. -/
theorem iteratedFDeriv_scaledChartCutoff
    (rho K : ℝ) (e : OpenPartialHomeomorph M E) (j : ℕ)
    {y : E} (hy : y ∈ e.target) :
    iteratedFDeriv ℝ j (scaledChartCutoff rho K e ∘ e.symm) y =
      iteratedFDeriv ℝ j (scaledCutoffProfile (E := E) rho K) y := by
  have heq : scaledChartCutoff rho K e ∘ e.symm =ᶠ[𝓝 y] scaledCutoffProfile rho K := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact scaledChartCutoff_chart_eq rho K e hz
  exact (heq.iteratedFDeriv ℝ j).eq_of_nhds

variable [ChartedSpace E M] [T2Space M]

/-- The literal normal-chart profile extended by zero is globally smooth on the
ORIGINAL manifold. The input is a genuine member of its maximal smooth atlas
whose target contains the given compact radius buffer.

Proof: the preceding compact containment puts the entire topological support
inside the open chart source. There the function equals the composition of the
actual smooth chart and the actual smooth scaled profile. Native
`contMDiff_of_tsupport` handles the zero germ at every other point.
Source: the smooth-zero-extension step of the scaled-bumps node. -/
theorem scaledChartCutoff_contMDiff
    (rho K : ℝ) (hrho : 0 < rho) (hK : 1 ≤ K)
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hbuffer : Metric.closedBall (0 : E) rho ⊆ e.target) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (scaledChartCutoff rho K e) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hsource : x ∈ e.source :=
    ((scaledChartCutoff_support_buffers rho K hrho hK e hbuffer).2.2.1 hx).1
  have hchart := contMDiffAt_of_mem_maximalAtlas he hsource
  have hcomp := ((scaledCutoffProfile_contDiff (E := E) rho K).contMDiff.contMDiffAt).comp x hchart
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hsource] with z hz
  exact scaledChartCutoff_on_source rho K e hz

/-- One sequence of constants controls the actual zero-extended bumps for EVERY
scale and EVERY genuine normal chart with the prescribed buffer. Its quantifier
order makes the constants independent of scale and center.

The conclusion includes `[0,1]`, the exact closed plateau, global smoothness,
compact topological support in both strict coordinate buffers, and the ALL-order
operator-norm derivative estimate for the actual chart representative. This is
the full scaled-profile/zero-extension leaf given the original normal-geometry
provider's genuine charts; it does not construct that provider or the later
square normalization. Source: the original scaled-bumps node.
-/
theorem exists_uniform_scaledChartCutoffs (rho : ℝ) (hrho : 0 < rho) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (K : ℝ), 1 ≤ K →
      ∀ (e : OpenPartialHomeomorph M E), e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M →
      Metric.closedBall (0 : E) rho ⊆ e.target →
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (scaledChartCutoff rho K e) ∧
      (∀ x, scaledChartCutoff rho K e x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x ∈ e.source ∩ e ⁻¹' Metric.closedBall 0 (rho / (10 * K)),
        scaledChartCutoff rho K e x = 1) ∧
      HasCompactSupport (scaledChartCutoff rho K e) ∧
      tsupport (scaledChartCutoff rho K e) ⊆
        e.symm '' Metric.closedBall 0 (3 * rho / (20 * K)) ∧
      tsupport (scaledChartCutoff rho K e) ⊆ e.source ∩ e ⁻¹' Metric.ball 0 (rho / (5 * K)) ∧
      tsupport (scaledChartCutoff rho K e) ⊆ e.source ∩ e ⁻¹' Metric.ball 0 (rho / (4 * K)) ∧
      ∀ j, ∀ y ∈ e.target,
        ‖iteratedFDeriv ℝ j (scaledChartCutoff rho K e ∘ e.symm) y‖ ≤ B j * K ^ j := by
  obtain ⟨B, hB, hbound⟩ := exists_scaledCutoffProfile_derivative_bounds (E := E) rho hrho
  refine ⟨B, hB, ?_⟩
  intro K hK e he hbuffer
  have hs := scaledChartCutoff_support_buffers rho K hrho hK e hbuffer
  refine ⟨scaledChartCutoff_contMDiff rho K hrho hK e he hbuffer,
    scaledChartCutoff_mem_Icc rho K e,
    fun x hx ↦ scaledChartCutoff_one rho K hrho hK e hx,
    hs.2.1, hs.1, hs.2.2.1, hs.2.2.2, ?_⟩
  intro j y hy
  rw [iteratedFDeriv_scaledChartCutoff rho K e j hy]
  exact hbound K hK j y

end ChartPullback

#print axioms scaledCutoffProfile_contDiff
#print axioms scaledCutoffProfile_mem_Icc
#print axioms scaledCutoffProfile_one
#print axioms scaledCutoffProfile_support
#print axioms scaledCutoffProfile_tsupport
#print axioms iteratedFDeriv_scaledCutoffProfile
#print axioms exists_scaledCutoffProfile_derivative_bounds
#print axioms scaledCutoffProfile_radius_nesting
#print axioms scaledChartCutoff_on_source
#print axioms scaledChartCutoff_off_source
#print axioms scaledChartCutoff_mem_Icc
#print axioms scaledChartCutoff_one
#print axioms scaledChartCutoff_support_buffers
#print axioms scaledChartCutoff_chart_eq
#print axioms iteratedFDeriv_scaledChartCutoff
#print axioms scaledChartCutoff_contMDiff
#print axioms exists_uniform_scaledChartCutoffs

end GlobalEmbedding.Offline
