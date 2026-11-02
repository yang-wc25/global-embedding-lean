import GlobalEmbedding.Paper.GeneralChartContDiff
import GlobalEmbedding.Paper.PaperCoordinateNormBridge
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Topology.Compactness.Compact
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Data.Finset.Max

/-!
# Quantitative local separation for perturbations of an immersion

Source: `literature/parallelizable-stable-plus-one/main.tex`, the first paragraph
of the proof of `thm:upgrade`, and the original node
`upgrade-uniform-diagonal-separation`.

The Euclidean estimate below directly uses the pinned Mathlib mean-value theorem.
The left inverse is subsequently produced from the actual injective derivative.
No injectivity of nearby maps is assumed.

This is an isolated offline candidate, not a main-library acceptance receipt.
-/

noncomputable section

open Filter Function Manifold Set
open scoped Topology ContDiff

namespace GlobalEmbedding.Offline

section Euclidean

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual projected displacement differs from the identity displacement by
at most the derivative error times the distance.

Proof: apply the existing convex mean-value theorem to `z ↦ A (g z) - z`.
Its derivative is produced by the chain and subtraction rules from the actual
`fderiv` of `g`. Source: the local lower-displacement argument in `thm:upgrade`.
-/
theorem projected_displacement_error
    (g : E → F) (A : F →L[ℝ] E) (s : Set E) (hs : Convex ℝ s) (q : ℝ)
    (hdiff : ∀ z ∈ s, DifferentiableAt ℝ g z)
    (hbound : ∀ z ∈ s, ‖A.comp (fderiv ℝ g z) - ContinuousLinearMap.id ℝ E‖ ≤ q)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖A (g x - g y) - (x - y)‖ ≤ q * ‖x - y‖ := by
  have hd (z : E) (hz : z ∈ s) :
      HasFDerivWithinAt (fun z ↦ A (g z) - z)
        (A.comp (fderiv ℝ g z) - ContinuousLinearMap.id ℝ E) s z :=
    ((A.hasFDerivAt.comp z (hdiff z hz).hasFDerivAt).sub (hasFDerivAt_id z)).hasFDerivWithinAt
  have hmean := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hbound hy hx
  calc
    ‖A (g x - g y) - (x - y)‖ = ‖(A (g x) - x) - (A (g y) - y)‖ := by
      rw [map_sub]
      congr 1
      abel
    _ ≤ q * ‖x - y‖ := hmean

/-- The quantitative lower displacement estimate for the same map and actual
derivative bounds. Proof: combine the preceding error estimate with the reverse
triangle inequality. Source: `upgrade-uniform-diagonal-separation`. -/
theorem projected_displacement_lower
    (g : E → F) (A : F →L[ℝ] E) (s : Set E) (hs : Convex ℝ s) (q : ℝ)
    (hdiff : ∀ z ∈ s, DifferentiableAt ℝ g z)
    (hbound : ∀ z ∈ s, ‖A.comp (fderiv ℝ g z) - ContinuousLinearMap.id ℝ E‖ ≤ q)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (1 - q) * ‖x - y‖ ≤ ‖A (g x - g y)‖ := by
  have herr := projected_displacement_error g A s hs q hdiff hbound hx hy
  have htriangle := norm_sub_norm_le (x - y) (A (g x - g y))
  rw [norm_sub_rev (x - y) (A (g x - g y))] at htriangle
  nlinarith

/-- Injectivity of the actual perturbed map follows from a derivative error
strictly less than one. Proof: equal image values force the nonnegative distance
to vanish in the lower bound. Empty and zero-dimensional domains are allowed.
Source: `upgrade-uniform-diagonal-separation`. -/
theorem injOn_of_projected_derivative_close
    (g : E → F) (A : F →L[ℝ] E) (s : Set E) (hs : Convex ℝ s) (q : ℝ) (hq : q < 1)
    (hdiff : ∀ z ∈ s, DifferentiableAt ℝ g z)
    (hbound : ∀ z ∈ s, ‖A.comp (fderiv ℝ g z) - ContinuousLinearMap.id ℝ E‖ ≤ q) :
    Set.InjOn g s := by
  intro x hx y hy hxy
  have h := projected_displacement_lower g A s hs q hdiff hbound hx hy
  rw [hxy, sub_self, map_zero, norm_zero] at h
  have hz : ‖x - y‖ = 0 := by
    have hn := norm_nonneg (x - y)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- An actual injective first derivative supplies a fixed positive radius,
continuous left inverse, and positive derivative tolerance which work for
**every** nearby differentiable map on that same closed ball.

Proof: produce a continuous left inverse of `Df(p)` by the native finite-target
theorem. Set `K=max(1,‖A‖)` and `epsilon=(4K)⁻¹`. Continuity of the actual
derivative gives a ball where `‖Df(z)-Df(p)‖<epsilon`; shrink it to a closed ball
inside the given neighborhood. If `‖Dg-Df‖<epsilon` there, the chain derivative
`A Dg` differs from the identity by at most `1/2`. The preceding actual MVT leaf
gives the lower bound and injectivity uniformly for all such `g`.

Source: `upgrade-uniform-diagonal-separation`, the fixed source chart estimate.
The maximum handles `‖A‖=0` and hence the zero-dimensional source correctly. -/
theorem exists_uniform_injective_closedBall
    [FiniteDimensional ℝ F]
    (f : E → F) (p : E) (hf : ContDiffAt ℝ 1 f p)
    (hinj : Function.Injective (fderiv ℝ f p))
    (s : Set E) (hs : s ∈ 𝓝 p) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall p r ⊆ s ∧
      ∃ A : F →L[ℝ] E, A.comp (fderiv ℝ f p) = ContinuousLinearMap.id ℝ E ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧
        ∀ g : E → F,
          (∀ z ∈ Metric.closedBall p r, DifferentiableAt ℝ g z) →
          (∀ z ∈ Metric.closedBall p r, ‖fderiv ℝ g z - fderiv ℝ f z‖ < epsilon) →
          (∀ x ∈ Metric.closedBall p r, ∀ y ∈ Metric.closedBall p r,
            (1 / 2 : ℝ) * ‖x - y‖ ≤ ‖A (g x - g y)‖) ∧
          Set.InjOn g (Metric.closedBall p r) := by
  obtain ⟨A, hleft⟩ :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
  have hbase : A.comp (fderiv ℝ f p) = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro v
    exact hleft v
  let K : ℝ := max 1 ‖A‖
  let epsilon : ℝ := (4 * K)⁻¹
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  have hKe : K * epsilon = (1 / 4 : ℝ) := by
    dsimp only [epsilon]
    field_simp
  have hderiv : ContinuousAt (fderiv ℝ f) p := hf.continuousAt_fderiv (by norm_num)
  have hnear : {z : E | ‖fderiv ℝ f z - fderiv ℝ f p‖ < epsilon} ∈ 𝓝 p := by
    simpa only [Set.preimage, Metric.mem_ball, dist_eq_norm] using
      hderiv.preimage_mem_nhds (Metric.ball_mem_nhds (fderiv ℝ f p) hepsilon)
  obtain ⟨r0, hr0, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hs hnear)
  have hclosed : Metric.closedBall p (r0 / 2) ⊆
      s ∩ {z | ‖fderiv ℝ f z - fderiv ℝ f p‖ < epsilon} :=
    (Metric.closedBall_subset_ball (half_lt_self hr0)).trans hball
  refine ⟨r0 / 2, half_pos hr0, fun z hz ↦ (hclosed hz).1, A, hbase,
    epsilon, hepsilon, ?_⟩
  intro g hg hclose
  have hbound (z : E) (hz : z ∈ Metric.closedBall p (r0 / 2)) :
      ‖A.comp (fderiv ℝ g z) - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 2 : ℝ) := by
    have hdiff : ‖fderiv ℝ g z - fderiv ℝ f p‖ ≤ epsilon + epsilon := by
      calc
        ‖fderiv ℝ g z - fderiv ℝ f p‖ =
            ‖(fderiv ℝ g z - fderiv ℝ f z) + (fderiv ℝ f z - fderiv ℝ f p)‖ := by
          congr 1
          abel
        _ ≤ ‖fderiv ℝ g z - fderiv ℝ f z‖ + ‖fderiv ℝ f z - fderiv ℝ f p‖ :=
          norm_add_le _ _
        _ ≤ epsilon + epsilon := add_le_add (hclose z hz).le (hclosed hz).2.le
    calc
      ‖A.comp (fderiv ℝ g z) - ContinuousLinearMap.id ℝ E‖ =
          ‖A.comp (fderiv ℝ g z - fderiv ℝ f p)‖ := by
        rw [ContinuousLinearMap.comp_sub, hbase]
      _ ≤ ‖A‖ * ‖fderiv ℝ g z - fderiv ℝ f p‖ := A.opNorm_comp_le _
      _ ≤ K * (epsilon + epsilon) :=
        mul_le_mul (le_max_right _ _) hdiff (norm_nonneg _) hK.le
      _ = (1 / 2 : ℝ) := by nlinarith [hKe]
  constructor
  · intro x hx y hy
    simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
      projected_displacement_lower g A _ (convex_closedBall p (r0 / 2))
        (1 / 2) hg hbound hx hy
  · exact injOn_of_projected_derivative_close g A _ (convex_closedBall p (r0 / 2))
      (1 / 2) (by norm_num) hg hbound

end Euclidean

section Manifold

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [BoundarylessManifold I M]

/-- Injectivity of the actual manifold immersion differential gives injectivity of
its centered chart derivative. Here the tangent spaces are identified by
the existing model casts; no coordinate immersion hypothesis is added.
Source: `upgrade-uniform-diagonal-separation`, passage to a source chart. -/
theorem centered_fderiv_injective
    (f : M → F) (p : M) (hf : MDifferentiableAt I 𝓘(ℝ, F) f p)
    (hinj : Function.Injective (mfderiv I 𝓘(ℝ, F) f p)) :
    Function.Injective (fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p p)) := by
  let C := fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p p)
  have hr : Set.range I ∈ 𝓝 (extChartAt I p p) :=
    range_mem_nhds_isInteriorPoint (BoundarylessManifold.isInteriorPoint (x := p))
  have hDC (v : TangentSpace I p) :
      tangentSpaceCastModel 𝓘(ℝ, F) (f p) (mfderiv I 𝓘(ℝ, F) f p v) =
        C (tangentSpaceCastModel I p v) := by
    dsimp only [C]
    rw [← fderivWithin_of_mem_nhds (𝕜 := ℝ) (f := f ∘ (extChartAt I p).symm) hr]
    simp [mfderiv, hf, writtenInExtChartAt]
  intro u v huv
  apply (tangentSpaceCastModel I p).symm.injective
  apply hinj
  apply (tangentSpaceCastModel 𝓘(ℝ, F) (f p)).injective
  simpa only [hDC, ContinuousLinearEquiv.apply_symm_apply] using huv

omit [BoundarylessManifold I M] in
/-- A smooth map has a smooth actual chart representative throughout the interior
of the chart target. This is the open differentiation domain used by the original
paper coordinate norm. Proof: compose with the existing smooth inverse chart and
remove its within restriction at an interior point.
Source: the coordinate norm convention and the upgrade proof's chart estimates. -/
theorem contDiffOn_interior_chart_representative
    [IsManifold I ∞ M] (f : M → F) (p : M)
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) :
    ContDiffOn ℝ ∞ (f ∘ (extChartAt I p).symm) (interior (extChartAt I p).target) := by
  intro z hz
  have hchart : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I p).symm z :=
    (contMDiffWithinAt_extChartAt_symm_target p (interior_subset hz)).contMDiffAt
      (mem_interior_iff_mem_nhds.mp hz)
  exact ((hf ((extChartAt I p).symm z)).comp z hchart).contDiffAt.contDiffWithinAt

/-- A centered chart of an actual smooth immersion contains a fixed open source
patch on which every sufficiently close smooth map is injective. The closeness
assumption is the actual operator norm of the difference of chart derivatives on
one fixed closed ball. Its radius and tolerance are produced before the nearby
map is quantified, so they work uniformly for the entire perturbation family.

Proof: injectivity of `mfderiv` supplies injectivity of the actual coordinate
derivative; apply the preceding quantitative Euclidean theorem and pull the inner
ball back through the chart. Boundarylessness supplies an open coordinate domain.
Source: `upgrade-uniform-diagonal-separation`. -/
theorem exists_uniform_injective_chart
    [FiniteDimensional ℝ F] [IsManifold I ∞ M]
    (f : M → F) (p : M) (hf : ContMDiff I 𝓘(ℝ, F) ∞ f)
    (hinj : Function.Injective (mfderiv I 𝓘(ℝ, F) f p)) :
    ∃ r epsilon : ℝ, 0 < r ∧ 0 < epsilon ∧
      Metric.closedBall (extChartAt I p p) r ⊆ interior (extChartAt I p).target ∧
      ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ W ⊆ (extChartAt I p).source ∧
        ∀ g : M → F, ContMDiff I 𝓘(ℝ, F) ∞ g →
          (∀ z ∈ Metric.closedBall (extChartAt I p p) r,
            ‖fderiv ℝ (g ∘ (extChartAt I p).symm) z -
              fderiv ℝ (f ∘ (extChartAt I p).symm) z‖ < epsilon) →
          Set.InjOn g W := by
  have hrange : Set.range I ∈ 𝓝 (extChartAt I p p) :=
    range_mem_nhds_isInteriorPoint (BoundarylessManifold.isInteriorPoint (x := p))
  have htarget : (extChartAt I p).target ∈ 𝓝 (extChartAt I p p) := by
    simpa only [nhdsWithin_eq_nhds.mpr hrange] using extChartAt_target_mem_nhdsWithin (I := I) p
  have hcf : ContDiffAt ℝ 1 (f ∘ (extChartAt I p).symm) (extChartAt I p p) :=
    (GlobalEmbedding.Paper.contDiffAt_general_chart_representative (hf p)).of_le (by simp)
  obtain ⟨r, hr, hball, A, _, epsilon, hepsilon, hstable⟩ :=
    exists_uniform_injective_closedBall (f ∘ (extChartAt I p).symm)
      (extChartAt I p p) hcf
      (centered_fderiv_injective f p ((hf p).mdifferentiableAt (by simp)) hinj)
      (interior (extChartAt I p).target) (interior_mem_nhds.mpr htarget)
  let W : Set M := (extChartAt I p).source ∩
    extChartAt I p ⁻¹' Metric.ball (extChartAt I p p) (r / 2)
  refine ⟨r, epsilon, hr, hepsilon, hball, W,
    isOpen_extChartAt_preimage' p Metric.isOpen_ball,
    ⟨mem_extChartAt_source p, Metric.mem_ball_self (half_pos hr)⟩,
    inter_subset_left, ?_⟩
  intro g hg hclose
  have hdiff (z : E) (hz : z ∈ Metric.closedBall (extChartAt I p p) r) :
      DifferentiableAt ℝ (g ∘ (extChartAt I p).symm) z := by
    have hzint := hball hz
    have hchart : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I p).symm z :=
      (contMDiffWithinAt_extChartAt_symm_target p (interior_subset hzint)).contMDiffAt
        (mem_interior_iff_mem_nhds.mp hzint)
    exact ((hg ((extChartAt I p).symm z)).comp z hchart).contDiffAt.differentiableAt (by simp)
  have hginj := (hstable (g ∘ (extChartAt I p).symm) hdiff hclose).2
  intro x hx y hy hxy
  apply (extChartAt I p).injOn hx.1 hy.1
  apply hginj
  · exact Metric.mem_closedBall.mpr (le_trans (Metric.mem_ball.mp hx.2).le (by linarith))
  · exact Metric.mem_closedBall.mpr (le_trans (Metric.mem_ball.mp hy.2).le (by linarith))
  · simpa only [Function.comp_apply, (extChartAt I p).left_inv hx.1,
      (extChartAt I p).left_inv hy.1] using hxy

/-- A compact smooth immersion admits one open symmetric neighborhood `V` of the
diagonal and finitely many positive chart derivative tolerances which ensure that
every sufficiently close smooth map separates all distinct pairs in `V`.
The complementary pair set is compact and contains no diagonal pair.

Proof: choose the preceding actual immersion charts at every point, take a finite
subcover, and let `V` be the union of the squares of those source patches. This
constructs the diagonal neighborhood rather than assuming local injectivity.
The resulting condition uses only actual Fréchet derivatives in finitely many
fixed charts. Source: `upgrade-uniform-diagonal-separation`, opening paragraph of
the upgrade proof. -/
theorem exists_uniform_diagonal_separation
    [FiniteDimensional ℝ F] [IsManifold I ∞ M] [CompactSpace M]
    (f : M → F) (hf : ContMDiff I 𝓘(ℝ, F) ∞ f)
    (hinj : ∀ p, Function.Injective (mfderiv I 𝓘(ℝ, F) f p)) :
    ∃ centers : Finset M, ∃ r epsilon : M → ℝ, ∃ V : Set (M × M),
      (∀ p, 0 < r p ∧ 0 < epsilon p ∧
        Metric.closedBall (extChartAt I p p) (r p) ⊆ interior (extChartAt I p).target) ∧
      IsOpen V ∧ Set.diagonal M ⊆ V ∧
      (∀ x y, (x, y) ∈ V → (y, x) ∈ V) ∧ IsCompact Vᶜ ∧
      (∀ z ∈ Vᶜ, z.1 ≠ z.2) ∧
      ∀ g : M → F, ContMDiff I 𝓘(ℝ, F) ∞ g →
        (∀ p ∈ centers, ∀ z ∈ Metric.closedBall (extChartAt I p p) (r p),
          ‖fderiv ℝ (g ∘ (extChartAt I p).symm) z -
            fderiv ℝ (f ∘ (extChartAt I p).symm) z‖ < epsilon p) →
        ∀ x y, (x, y) ∈ V → g x = g y → x = y := by
  classical
  choose r epsilon hr hepsilon hball W hW hmem hsrc hstable using
    fun p ↦ exists_uniform_injective_chart f p hf (hinj p)
  obtain ⟨centers, hcover⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hmem x⟩)
  let V : Set (M × M) := ⋃ p ∈ centers, W p ×ˢ W p
  have hV : IsOpen V := isOpen_biUnion fun p _ ↦ (hW p).prod (hW p)
  have hdiag : Set.diagonal M ⊆ V := by
    apply Set.diagonal_subset_iff.mpr
    intro x
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ x))
    obtain ⟨hpc, hpx⟩ := Set.mem_iUnion.mp hp
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hpc, hpx, hpx⟩⟩
  refine ⟨centers, r, epsilon, V, fun p ↦ ⟨hr p, hepsilon p, hball p⟩,
    hV, hdiag, ?_, hV.isClosed_compl.isCompact, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hxy
    obtain ⟨hpc, hpair⟩ := Set.mem_iUnion.mp hp
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hpc, hpair.2, hpair.1⟩⟩
  · intro z hz hzz
    exact hz (hdiag hzz)
  · intro g hg hclose x y hxy hgeq
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hxy
    obtain ⟨hpc, hpair⟩ := Set.mem_iUnion.mp hp
    exact hstable p g hg (hclose p hpc) hpair.1 hpair.2 hgeq

end Manifold

section CanonicalCoordinateNorm

open GlobalEmbedding.Paper

/-- On compact norm-evaluation domains contained in open smooth differentiation
domains, the ORIGINAL finite-atlas coordinate norm is finite at every order.
Proof: actual iterated derivatives are continuous on the open domains and bounded
on the compact domains; the existing paper norm equivalence gives finiteness.
Source: the paper's finite atlas coordinate norm convention. -/
theorem paperAtlasCj_ne_top_of_compact
    {ι : Type*} [Fintype ι] {n N : ℕ} (j : ℕ)
    (f : ι → (Fin n → ℝ) → Fin N → ℝ)
    (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hS : ∀ i, IsCompact (S i))
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) :
    paperAtlasCj j f O S ≠ ⊤ := by
  apply (paperAtlasCj_ne_top_iff j f O S hO hSO hf).mpr
  intro i k _
  have hc : ContinuousOn (fun z ↦ ‖iteratedFDeriv ℝ k (f i) z‖) (S i) :=
    ((ContinuousOn.continuousOn_iteratedFDeriv (hf i) (hO i) (by simp)).norm).mono (hSO i)
  apply ((hS i).bddAbove_image hc).mono
  rintro a ⟨z, rfl⟩
  exact ⟨z, z.property, rfl⟩

/-- The ORIGINAL componentwise finite-atlas `C¹` maximum controls the actual
operator norm of every chart derivative difference, with the fixed factor `1+n`
and no chart-count factor.

Proof: use the existing `paperAtlasCj_finiteCjNorm_bound` and the existing actual
finite-derivative supremum specification; identify the order-one derivative with
`fderiv`, then use its subtraction rule. Finiteness is explicit because the
canonical paper gauge has values in `ENNReal`. This is the native norm interface
needed by `exists_uniform_diagonal_separation`, not a replacement norm.
Source: `upgrade-uniform-diagonal-separation` and the paper's coordinate norm
convention. -/
theorem paperAtlasC1_derivative_difference_bound
    {ι : Type*} [Fintype ι] {n N : ℕ}
    (f g : ι → (Fin n → ℝ) → Fin N → ℝ)
    (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (O i))
    (hfinite : paperAtlasCj 1 (fun i ↦ g i - f i) O S ≠ ⊤)
    (i : ι) {z : Fin n → ℝ} (hz : z ∈ S i) :
    ‖fderiv ℝ (g i) z - fderiv ℝ (f i) z‖ ≤
      (1 + (n : ℝ)) * (paperAtlasCj 1 (fun i ↦ g i - f i) O S).toReal := by
  have hd (i : ι) : ContDiffOn ℝ ∞ (g i - f i) (O i) := (hg i).sub (hf i)
  have hb := (paperAtlasCj_ne_top_iff 1 (fun i ↦ g i - f i) O S hO hSO hd).mp hfinite
  have hnorm := (finiteCjNorm_specification 1 (g i - f i) (S i) (hb i)).2.1
    1 (le_refl _) z hz
  rw [norm_iteratedFDeriv_one] at hnorm
  have hdf : DifferentiableAt ℝ (f i) z :=
    ((hf i).differentiableOn (by simp) z (hSO i hz)).differentiableAt
      ((hO i).mem_nhds (hSO i hz))
  have hdg : DifferentiableAt ℝ (g i) z :=
    ((hg i).differentiableOn (by simp) z (hSO i hz)).differentiableAt
      ((hO i).mem_nhds (hSO i hz))
  rw [fderiv_sub hdg hdf] at hnorm
  exact hnorm.trans (by
    simpa [Finset.sum_range_succ] using
      paperAtlasCj_finiteCjNorm_bound 1 (fun i ↦ g i - f i) O S hO hSO hd hfinite i)

/-- A smooth compact immersion into the ORIGINAL Euclidean target admits one
uniform open symmetric diagonal neighborhood for every smooth map sufficiently
close in the ORIGINAL componentwise finite-atlas `C¹` norm.

The atlas, its compact closed-ball evaluation domains, and the positive tolerance
are all fixed before the perturbed map is quantified. The literal paper norm is
proved finite on those domains. Its first-derivative control supplies the proven
local quantitative injectivity, so nearby-map injectivity is not assumed.

Proof: express the Euclidean target in its existing scalar-coordinate continuous
linear equivalence (preserving the actual immersion differential), use the finite
chart separation theorem, take the positive minimum of its finite tolerances and
one, and divide by `1+n`. The native paper norm bound then implies every chart
derivative tolerance. No positive dimension or nonempty source is assumed.
Source: `upgrade-uniform-diagonal-separation`, the first paragraph of `thm:upgrade`.
-/
theorem exists_paperAtlasC1_uniform_diagonal_separation
    {n N : ℕ} {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (Fin n → ℝ) H}
    [TopologicalSpace M] [ChartedSpace H M] [BoundarylessManifold I M]
    [IsManifold I ∞ M] [CompactSpace M]
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f)
    (hinj : ∀ p, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f p)) :
    ∃ centers : Finset M, ∃ r : M → ℝ, ∃ delta : ℝ, ∃ V : Set (M × M),
      0 < delta ∧
      (∀ p, 0 < r p ∧
        Metric.closedBall (extChartAt I p p) (r p) ⊆ interior (extChartAt I p).target) ∧
      IsOpen V ∧ Set.diagonal M ⊆ V ∧
      (∀ x y, (x, y) ∈ V → (y, x) ∈ V) ∧ IsCompact Vᶜ ∧
      (∀ z ∈ Vᶜ, z.1 ≠ z.2) ∧
      ∀ g : M → EuclideanSpace ℝ (Fin N),
        ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ g →
        let e := EuclideanSpace.equiv (Fin N) ℝ
        let cf : centers → (Fin n → ℝ) → Fin N → ℝ :=
          fun p ↦ e ∘ f ∘ (extChartAt I p.1).symm
        let cg : centers → (Fin n → ℝ) → Fin N → ℝ :=
          fun p ↦ e ∘ g ∘ (extChartAt I p.1).symm
        let O : centers → Set (Fin n → ℝ) := fun p ↦ interior (extChartAt I p.1).target
        let S : centers → Set (Fin n → ℝ) :=
          fun p ↦ Metric.closedBall (extChartAt I p.1 p.1) (r p.1)
        paperAtlasCj 1 (fun p ↦ cg p - cf p) O S ≠ ⊤ ∧
          ((paperAtlasCj 1 (fun p ↦ cg p - cf p) O S).toReal < delta →
            ∀ x y, (x, y) ∈ V → g x = g y → x = y) := by
  classical
  let e := EuclideanSpace.equiv (Fin N) ℝ
  have hfe : ContMDiff I 𝓘(ℝ, Fin N → ℝ) ∞ (e ∘ f) :=
    e.contDiff.comp_contMDiff hf
  have hinje (p : M) : Function.Injective (mfderiv I 𝓘(ℝ, Fin N → ℝ) (e ∘ f) p) := by
    rw [mfderiv_comp p e.mdifferentiableAt ((hf p).mdifferentiableAt (by simp)),
      ContinuousLinearEquiv.mfderiv_eq]
    exact e.injective.comp (hinj p)
  obtain ⟨centers, r, epsilon, V, hlocal, hV, hdiag, hsym, hcompact, hoff, hstable⟩ :=
    exists_uniform_diagonal_separation (e ∘ f) hfe hinje
  let tolerances : Finset ℝ := insert 1 (centers.image epsilon)
  have htne : tolerances.Nonempty := Finset.insert_nonempty _ _
  let epsilon0 : ℝ := tolerances.min' htne
  have hepsilon0 : 0 < epsilon0 := by
    apply (Finset.lt_min'_iff tolerances htne).mpr
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact zero_lt_one
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
      exact (hlocal p).2.1
  have hmin (p : M) (hp : p ∈ centers) : epsilon0 ≤ epsilon p :=
    Finset.min'_le tolerances _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  have hdim : 0 < 1 + (n : ℝ) := by positivity
  refine ⟨centers, r, epsilon0 / (1 + (n : ℝ)), V,
    div_pos hepsilon0 hdim, fun p ↦ ⟨(hlocal p).1, (hlocal p).2.2⟩,
    hV, hdiag, hsym, hcompact, hoff, ?_⟩
  intro g hg
  let cf : centers → (Fin n → ℝ) → Fin N → ℝ :=
    fun p ↦ e ∘ f ∘ (extChartAt I p.1).symm
  let cg : centers → (Fin n → ℝ) → Fin N → ℝ :=
    fun p ↦ e ∘ g ∘ (extChartAt I p.1).symm
  let O : centers → Set (Fin n → ℝ) := fun p ↦ interior (extChartAt I p.1).target
  let S : centers → Set (Fin n → ℝ) :=
    fun p ↦ Metric.closedBall (extChartAt I p.1 p.1) (r p.1)
  change paperAtlasCj 1 (fun p ↦ cg p - cf p) O S ≠ ⊤ ∧
    ((paperAtlasCj 1 (fun p ↦ cg p - cf p) O S).toReal < epsilon0 / (1 + (n : ℝ)) →
      ∀ x y, (x, y) ∈ V → g x = g y → x = y)
  have hge : ContMDiff I 𝓘(ℝ, Fin N → ℝ) ∞ (e ∘ g) :=
    e.contDiff.comp_contMDiff hg
  have hcf (p : centers) : ContDiffOn ℝ ∞ (cf p) (O p) :=
    contDiffOn_interior_chart_representative (e ∘ f) p.1 hfe
  have hcg (p : centers) : ContDiffOn ℝ ∞ (cg p) (O p) :=
    contDiffOn_interior_chart_representative (e ∘ g) p.1 hge
  have hO (p : centers) : IsOpen (O p) := isOpen_interior
  have hSO (p : centers) : S p ⊆ O p := (hlocal p.1).2.2
  have hS (p : centers) : IsCompact (S p) := isCompact_closedBall _ _
  have hfinite : paperAtlasCj 1 (fun p ↦ cg p - cf p) O S ≠ ⊤ :=
    paperAtlasCj_ne_top_of_compact 1 _ O S hO hSO hS (fun p ↦ (hcg p).sub (hcf p))
  refine ⟨hfinite, ?_⟩
  intro hsmall x y hxy hgeq
  apply hstable (e ∘ g) hge ?_ x y hxy (congrArg e hgeq)
  intro p hp z hz
  have hbound := paperAtlasC1_derivative_difference_bound cf cg O S hO hSO hcf hcg
    hfinite ⟨p, hp⟩ hz
  have hsmall' : (1 + (n : ℝ)) * (paperAtlasCj 1 (fun p ↦ cg p - cf p) O S).toReal <
      epsilon0 := by
    simpa only [mul_comm] using (lt_div_iff₀ hdim).mp hsmall
  exact hbound.trans_lt (hsmall'.trans_le (hmin p hp))

end CanonicalCoordinateNorm

#print axioms projected_displacement_error
#print axioms projected_displacement_lower
#print axioms injOn_of_projected_derivative_close
#print axioms exists_uniform_injective_closedBall
#print axioms centered_fderiv_injective
#print axioms contDiffOn_interior_chart_representative
#print axioms exists_uniform_injective_chart
#print axioms exists_uniform_diagonal_separation
#print axioms paperAtlasC1_derivative_difference_bound
#print axioms paperAtlasCj_ne_top_of_compact
#print axioms exists_paperAtlasC1_uniform_diagonal_separation

end GlobalEmbedding.Offline
