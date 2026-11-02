import GlobalEmbedding.Paper.MatrixSmoothHessianCorrection
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Native manifold families of small Hessian-controlled corrections

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix` proof,
lines 311–315. Parent DAG node: `matrix-uniform-small-residual-correction`.
-/

open Set Metric
open scoped Topology ContDiff Manifold

namespace GlobalEmbedding.Paper

/-- The actual small correction is globally smooth on a native parameter manifold and is
constant on equal fiber equations, with one quantitative radius and residual bound.

Proof: obtain pointwise roots from the accepted normed Hessian correction applied to
constant parameter families. In each actual manifold chart apply the same accepted theorem
to the pulled-back actual joint equation. Its smooth local solution and the global selected
root solve the same fiber equation in the same ball, so uniqueness identifies them. Compose
with the native smooth chart and use eventual equality to prove native smoothness of the
selected map. Equation-preserving equality follows from uniqueness in the same ball.
Source: `prop:matrix` proof, lines 311–315. -/
theorem manifold_hessian_small_residual_correction
    {P Q X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [TopologicalSpace Q] [ChartedSpace P Q] [IsManifold 𝓘(ℝ, P) ∞ Q]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (f : Q → X → X) (A : Q → X ≃L[ℝ] X)
    (r L K ε : ℝ) (hr : 0 < r) (hL : 0 < L) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hsmall : 4 * L * K * r ≤ 1) (hresSmall : L * ε ≤ r / 2)
    (hf : ContMDiff ((𝓘(ℝ, P)).prod 𝓘(ℝ, X)) 𝓘(ℝ, X) ∞ (Function.uncurry f))
    (hA : ∀ q, (A q : X →L[ℝ] X) = fderiv ℝ (f q) 0)
    (hAinv : ∀ q, ‖(A q).symm.toContinuousLinearMap‖ ≤ L)
    (hHess : ∀ q, ∀ x ∈ closedBall (0 : X) r,
      ‖fderiv ℝ (fderiv ℝ (f q)) x‖ ≤ K)
    (hres : ∀ q, ‖f q 0‖ ≤ ε) :
    ∃ c : Q → X, ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, X) ∞ c ∧
      (∀ q, f q (c q) = 0 ∧ ‖c q‖ ≤ (4 / 3 : ℝ) * L * ε ∧
        ‖c q‖ ≤ 2 * r / 3 ∧ (∀ y : X, ‖y‖ ≤ r → f q y = 0 → y = c q)) ∧
      (∀ q q', (∀ x, f q x = f q' x) → c q = c q') := by
  have hroot (q : Q) : ∃ x : X, f q x = 0 ∧ ‖x‖ ≤ (4 / 3 : ℝ) * L * ε ∧
      ‖x‖ ≤ 2 * r / 3 ∧ (∀ y : X, ‖y‖ ≤ r → f q y = 0 → y = x) := by
    have hs : ContDiff ℝ ∞ (f q) := by
      exact (hf.comp (contMDiff_const.prodMk contMDiff_id)).contDiff
    have hconst : ContDiffOn ℝ ∞
        (Function.uncurry (fun _ : ℝ ↦ f q)) (univ ×ˢ univ) :=
      (hs.comp contDiff_snd).contDiffOn
    obtain ⟨g, _, hg, _⟩ := smooth_hessian_small_residual_correction univ isOpen_univ
      (fun _ : ℝ ↦ f q) (fun _ ↦ A q) r L K ε hr hL hK hε hsmall hresSmall hconst
      (fun _ _ ↦ hA q) (fun _ _ ↦ hAinv q) (fun _ _ ↦ hHess q) (fun _ _ ↦ hres q)
    exact ⟨g 0, hg 0 (mem_univ _)⟩
  choose c hc using hroot
  have hcsmooth : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, X) ∞ c := by
    intro q
    let e := chartAt P q
    have hinv : ContMDiffOn 𝓘(ℝ, P) 𝓘(ℝ, P) ∞ e.symm e.target :=
      contMDiffOn_chart_symm
    have hpair : ContMDiffOn 𝓘(ℝ, P × X) ((𝓘(ℝ, P)).prod 𝓘(ℝ, X)) ∞
        (fun z : P × X ↦ (e.symm z.1, z.2)) (e.target ×ˢ univ) := by
      have hfst : ContMDiffOn 𝓘(ℝ, P × X) 𝓘(ℝ, P) ∞
          (Prod.fst : P × X → P) (e.target ×ˢ univ) :=
        contDiff_fst.contMDiff.contMDiffOn
      have hsnd : ContMDiffOn 𝓘(ℝ, P × X) 𝓘(ℝ, X) ∞
          (Prod.snd : P × X → X) (e.target ×ˢ univ) :=
        contDiff_snd.contMDiff.contMDiffOn
      exact (hinv.comp hfst (fun z hz ↦ hz.1)).prodMk hsnd
    have hchart : ContDiffOn ℝ ∞ (Function.uncurry (fun y : P ↦ f (e.symm y)))
        (e.target ×ˢ univ) := (hf.comp_contMDiffOn hpair).contDiffOn
    obtain ⟨g, hg, hzero, _⟩ := smooth_hessian_small_residual_correction
      e.target e.open_target (fun y : P ↦ f (e.symm y)) (fun y ↦ A (e.symm y))
      r L K ε hr hL hK hε hsmall hresSmall hchart
      (fun y _ ↦ hA (e.symm y)) (fun y _ ↦ hAinv (e.symm y))
      (fun y _ ↦ hHess (e.symm y)) (fun y _ ↦ hres (e.symm y))
    have hq : q ∈ e.source := mem_chart_source P q
    have htarget : e q ∈ e.target := e.map_source hq
    have hgAt : ContDiffAt ℝ ∞ g (e q) := hg.contDiffAt (e.open_target.mem_nhds htarget)
    have heAt : ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, P) ∞ e q :=
      (contMDiffOn_chart (I := 𝓘(ℝ, P))).contMDiffAt (e.open_source.mem_nhds hq)
    have hcomp := hgAt.contMDiffAt.comp q heAt
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hq] with z hz
    have hgz := hzero (e z) (e.map_source hz)
    have hgzroot : f z (g (e z)) = 0 := by simpa only [e.left_inv hz] using hgz.1
    have hgzsmall : ‖g (e z)‖ ≤ r := by linarith [hgz.2.2.1]
    exact ((hc z).2.2.2 (g (e z)) hgzsmall hgzroot).symm
  refine ⟨c, hcsmooth, hc, ?_⟩
  intro q q' heq
  apply (hc q').2.2.2
  · linarith [(hc q).2.2.1]
  · rw [← heq, (hc q).1]

#print axioms manifold_hessian_small_residual_correction

end GlobalEmbedding.Paper
