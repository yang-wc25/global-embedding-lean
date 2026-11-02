import GlobalEmbedding.Paper.MatrixExponentialMomentMinimizer
import GlobalEmbedding.Paper.MatrixExponentialMomentCalculus
import GlobalEmbedding.Paper.BalancedImplicitLocalSolution
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth dependence of the genuine exponential moment inverse

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines345–350.
The actual positive Hessian is invertible, and genuine IFT branches agree by strict injectivity.
-/

noncomputable section
open Set Filter
open scoped Manifold Topology ContDiff RealInnerProductSpace BigOperators

namespace GlobalEmbedding.Paper

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual positive Hessian is a continuous linear equivalence, including dimension zero. -/
theorem matrixExponentialHessian_isInvertible (v : ι → E)
    (hspan : ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v i, u⟫) (x : E) :
    (matrixExponentialHessian v x).IsInvertible := by
  have hinj : Function.Injective (matrixExponentialHessian v x) := by
    intro u w huw
    by_contra hn
    have hp := matrixExponentialHessian_pos v hspan x (u - w) (sub_ne_zero.mpr hn)
    have hz : matrixExponentialHessian v x (u - w) = 0 := by
      rw [map_sub, huw, sub_self]
    rw [hz, inner_zero_right] at hp
    exact lt_irrefl _ hp
  let e := (LinearEquiv.ofBijective (matrixExponentialHessian v x).toLinearMap
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

/-- Uniqueness identifies every actual root function with the genuinely smooth local IFT branch. -/
theorem matrix_exponential_moment_root_contDiffOn
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (P : Set B) (hP : IsOpen P) (v : B → ι → E) (y : B → E)
    (hv : ∀ i, ContDiffOn ℝ ∞ (fun p ↦ v p i) P) (hy : ContDiffOn ℝ ∞ y P)
    (hspan : ∀ p ∈ P, ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v p i, u⟫)
    (l : B → E) (hl : ∀ p ∈ P, matrixExponentialMoment (v p) (l p) = y p) :
    ContDiffOn ℝ ∞ l P := by
  let : CompleteSpace B := FiniteDimensional.complete ℝ B
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let G : B × E → E := fun z ↦ matrixExponentialMoment (v z.1) z.2 - y z.1
  have hfst : ContDiffOn ℝ ∞ (Prod.fst : B × E → B) (P ×ˢ univ) :=
    contDiff_fst.contDiffOn
  have hsnd : ContDiffOn ℝ ∞ (Prod.snd : B × E → E) (P ×ˢ univ) :=
    contDiff_snd.contDiffOn
  have hvi (i : ι) : ContDiffOn ℝ ∞ (fun z : B × E ↦ v z.1 i) (P ×ˢ univ) :=
    (hv i).comp hfst (fun _ hz ↦ hz.1)
  have hG : ContDiffOn ℝ ∞ G (P ×ˢ univ) := by
    apply ContDiffOn.sub
    · exact ContDiffOn.sum (fun i _ ↦ ((hvi i).inner ℝ hsnd).exp.smul (hvi i))
    · exact hy.comp hfst (fun _ hz ↦ hz.1)
  intro p hp
  have hzero : G (p, l p) = 0 := sub_eq_zero.mpr (hl p hp)
  have hd : HasFDerivAt G (fderiv ℝ G (p, l p)) (p, l p) :=
    (hG.contDiffAt ((hP.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)).differentiableAt
      (by simp) |>.hasFDerivAt
  have hpair : HasFDerivAt (fun x : E ↦ (p, x))
      (ContinuousLinearMap.inr ℝ B E) (l p) := by
    have heq : ContinuousLinearMap.inr ℝ B E =
        (0 : E →L[ℝ] B).prod (ContinuousLinearMap.id ℝ E) := by
      ext u <;> rfl
    rw [heq]
    exact (hasFDerivAt_const p (l p)).prodMk (hasFDerivAt_id (l p))
  have he : fderiv ℝ G (p, l p) ∘L ContinuousLinearMap.inr ℝ B E =
      matrixExponentialHessian (v p) (l p) :=
    (hd.comp (l p) hpair).unique
      ((matrixExponentialMoment_hasFDerivAt (v p) (l p)).sub_const (y p))
  have hinv : (fderiv ℝ G (p, l p) ∘L ContinuousLinearMap.inr ℝ B E).IsInvertible := by
    rw [he]
    exact matrixExponentialHessian_isInvertible (v p) (hspan p hp) (l p)
  obtain ⟨U, hU, hpU, hUP, g, hg, _, hroot⟩ :=
    balanced_implicit_local_solution P hP G hG p (l p) hp hzero hinv
  have hlg : ∀ q ∈ U, l q = g q := by
    intro q hq
    apply matrixExponentialMoment_injective (v q) (hspan q (hUP hq))
    exact (hl q (hUP hq)).trans (sub_eq_zero.mp (hroot q hq)).symm
  exact ((hg.congr hlg).contDiffAt (hU.mem_nhds hpU)).contDiffWithinAt

/-- Native manifold smoothness follows in genuine charts, without a supplied smooth root. -/
theorem matrix_exponential_moment_root_contMDiff
    {N Q : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    [TopologicalSpace Q] [ChartedSpace N Q] [IsManifold 𝓘(ℝ, N) ∞ Q]
    (v : Q → ι → E) (y : Q → E)
    (hv : ∀ i, ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, E) ∞ (fun q ↦ v q i))
    (hy : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, E) ∞ y)
    (hspan : ∀ q, ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v q i, u⟫)
    (l : Q → E) (hl : ∀ q, matrixExponentialMoment (v q) (l q) = y q) :
    ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, E) ∞ l := by
  intro q
  let e := chartAt N q
  have hinv : ContMDiffOn 𝓘(ℝ, N) 𝓘(ℝ, N) ∞ e.symm e.target :=
    contMDiffOn_chart_symm
  have hvc (i : ι) : ContDiffOn ℝ ∞ (fun z ↦ v (e.symm z) i) e.target :=
    ((hv i).comp_contMDiffOn hinv).contDiffOn
  have hyc : ContDiffOn ℝ ∞ (fun z ↦ y (e.symm z)) e.target :=
    (hy.comp_contMDiffOn hinv).contDiffOn
  have hc := matrix_exponential_moment_root_contDiffOn e.target e.open_target
    (fun z ↦ v (e.symm z)) (fun z ↦ y (e.symm z)) hvc hyc
    (fun z _ ↦ hspan (e.symm z)) (fun z ↦ l (e.symm z)) (fun z _ ↦ hl (e.symm z))
  have hq : q ∈ e.source := mem_chart_source N q
  have ht : e q ∈ e.target := e.map_source hq
  have ha := (hc.contDiffAt (e.open_target.mem_nhds ht)).contMDiffAt
  have he : ContMDiffAt 𝓘(ℝ, N) 𝓘(ℝ, N) ∞ e q :=
    (contMDiffOn_chart (I := 𝓘(ℝ, N))).contMDiffAt (e.open_source.mem_nhds hq)
  apply (ha.comp q he).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hq] with z hz
  simp only [Function.comp_apply, e.left_inv hz]

/-- The actual inverse chosen from the literal moment map, with data defined everywhere. -/
def matrixExponentialMomentInverse (v : ι → E) (y : E) : E :=
  Function.invFun (matrixExponentialMoment v) y

/-- Coercive minimization proves the chosen actual inverse solves the required moment equation. -/
theorem matrixExponentialMomentInverse_moment [Nonempty ι] (v : ι → E)
    (hspan : ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v i, u⟫) (y : E) :
    matrixExponentialMoment v (matrixExponentialMomentInverse v y) = y :=
  Function.invFun_eq (matrixExponentialMoment_surjective v hspan y)

/-- The actual inverse is smooth on every open smooth parameter domain. -/
theorem matrixExponentialMomentInverse_contDiffOn [Nonempty ι]
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (P : Set B) (hP : IsOpen P) (v : B → ι → E) (y : B → E)
    (hv : ∀ i, ContDiffOn ℝ ∞ (fun p ↦ v p i) P) (hy : ContDiffOn ℝ ∞ y P)
    (hspan : ∀ p ∈ P, ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v p i, u⟫) :
    ContDiffOn ℝ ∞ (fun p ↦ matrixExponentialMomentInverse (v p) (y p)) P :=
  matrix_exponential_moment_root_contDiffOn P hP v y hv hy hspan _
    (fun p hp ↦ matrixExponentialMomentInverse_moment (v p) (hspan p hp) (y p))

/-- The genuine inverse is native smooth on the original finite-dimensional manifold. -/
theorem matrixExponentialMomentInverse_contMDiff [Nonempty ι]
    {N Q : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    [TopologicalSpace Q] [ChartedSpace N Q] [IsManifold 𝓘(ℝ, N) ∞ Q]
    (v : Q → ι → E) (y : Q → E)
    (hv : ∀ i, ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, E) ∞ (fun q ↦ v q i))
    (hy : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, E) ∞ y)
    (hspan : ∀ q, ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v q i, u⟫) :
    ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, E) ∞
      (fun q ↦ matrixExponentialMomentInverse (v q) (y q)) :=
  matrix_exponential_moment_root_contMDiff v y hv hy hspan _
    (fun q ↦ matrixExponentialMomentInverse_moment (v q) (hspan q) (y q))

omit [FiniteDimensional ℝ E] in
/-- Actual orbit-invariant data give the same actual inverse on every point of an orbit. -/
theorem matrixExponentialMomentInverse_flow {Q : Type*} (R : ℝ → Q → Q)
    (v : Q → ι → E) (y : Q → E)
    (hv : ∀ t q i, v (R t q) i = v q i) (hy : ∀ t q, y (R t q) = y q) (t : ℝ) (q : Q) :
    matrixExponentialMomentInverse (v (R t q)) (y (R t q)) =
      matrixExponentialMomentInverse (v q) (y q) := by
  rw [hy t q, show v (R t q) = v q from funext (hv t q)]

#print axioms matrixExponentialMomentInverse_moment
#print axioms matrixExponentialMomentInverse_contDiffOn
#print axioms matrixExponentialMomentInverse_contMDiff
#print axioms matrixExponentialMomentInverse_flow
#print axioms matrix_exponential_moment_root_contMDiff
#print axioms matrixExponentialHessian_isInvertible
#print axioms matrix_exponential_moment_root_contDiffOn

end GlobalEmbedding.Paper
