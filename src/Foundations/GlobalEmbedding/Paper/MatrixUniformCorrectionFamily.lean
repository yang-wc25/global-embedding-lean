import GlobalEmbedding.Paper.MatrixManifoldHessianCorrection
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Uniform vanishing of the actual small correction family

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines 311–315.
DAG node: `matrix-uniform-correction-family`.
-/

open Set Metric Filter
open scoped Topology ContDiff Manifold

namespace GlobalEmbedding.Paper

/-- Eventual actual uniform Hessian/inverse bounds and vanishing residuals give actual
smooth small roots converging uniformly to zero, including noncompact parameter manifolds.

Proof: at each index satisfying the actual equation data, use the native manifold
Hessian correction. At other indices choose the smooth zero function. This gives a
globally defined family and retains the actual equation/uniqueness/basicness eventually.
The common bound (4/3)Lε tends to zero; the metric characterization of native uniform
convergence proves the final conclusion. No regularity in the index is used.
Source: `prop:matrix`, lines 311–315. -/
theorem uniform_correction_family
    {ι P Q X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [TopologicalSpace Q] [ChartedSpace P Q] [IsManifold 𝓘(ℝ, P) ∞ Q]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (l : Filter ι) (f : ι → Q → X → X) (A : ι → Q → X ≃L[ℝ] X)
    (r L K : ℝ) (ε : ι → ℝ) (hr : 0 < r) (hL : 0 < L) (hK : 0 ≤ K)
    (hsmall : 4 * L * K * r ≤ 1) (hlim : Tendsto ε l (𝓝 0))
    (hdata : ∀ᶠ i in l, 0 ≤ ε i ∧ L * ε i ≤ r / 2 ∧
      ContMDiff ((𝓘(ℝ, P)).prod 𝓘(ℝ, X)) 𝓘(ℝ, X) ∞ (Function.uncurry (f i)) ∧
      (∀ q, (A i q : X →L[ℝ] X) = fderiv ℝ (f i q) 0) ∧
      (∀ q, ‖(A i q).symm.toContinuousLinearMap‖ ≤ L) ∧
      (∀ q, ∀ x ∈ closedBall (0 : X) r, ‖fderiv ℝ (fderiv ℝ (f i q)) x‖ ≤ K) ∧
      (∀ q, ‖f i q 0‖ ≤ ε i)) :
    ∃ c : ι → Q → X,
      (∀ i, ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, X) ∞ (c i)) ∧
      (∀ᶠ i in l,
        (∀ q, f i q (c i q) = 0 ∧ ‖c i q‖ ≤ (4 / 3 : ℝ) * L * ε i ∧
          ‖c i q‖ ≤ 2 * r / 3 ∧
          (∀ y : X, ‖y‖ ≤ r → f i q y = 0 → y = c i q)) ∧
        (∀ q q', (∀ x, f i q x = f i q' x) → c i q = c i q')) ∧
      TendstoUniformly c (fun _ : Q ↦ (0 : X)) l := by
  classical
  let Good (i : ι) : Prop := 0 ≤ ε i ∧ L * ε i ≤ r / 2 ∧
    ContMDiff ((𝓘(ℝ, P)).prod 𝓘(ℝ, X)) 𝓘(ℝ, X) ∞ (Function.uncurry (f i)) ∧
    (∀ q, (A i q : X →L[ℝ] X) = fderiv ℝ (f i q) 0) ∧
    (∀ q, ‖(A i q).symm.toContinuousLinearMap‖ ≤ L) ∧
    (∀ q, ∀ x ∈ closedBall (0 : X) r, ‖fderiv ℝ (fderiv ℝ (f i q)) x‖ ≤ K) ∧
    (∀ q, ‖f i q 0‖ ≤ ε i)
  have hex (i : ι) : ∃ c : Q → X, ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, X) ∞ c ∧
      (Good i →
        (∀ q, f i q (c q) = 0 ∧ ‖c q‖ ≤ (4 / 3 : ℝ) * L * ε i ∧
          ‖c q‖ ≤ 2 * r / 3 ∧ (∀ y : X, ‖y‖ ≤ r → f i q y = 0 → y = c q)) ∧
        (∀ q q', (∀ x, f i q x = f i q' x) → c q = c q')) := by
    by_cases hi : Good i
    · obtain ⟨c, hc, hroot, hbasic⟩ := manifold_hessian_small_residual_correction
        (f i) (A i) r L K (ε i) hr hL hK hi.1 hsmall hi.2.1 hi.2.2.1
        hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2.1 hi.2.2.2.2.2.2
      exact ⟨c, hc, fun _ ↦ ⟨hroot, hbasic⟩⟩
    · exact ⟨fun _ ↦ 0, contMDiff_const, fun h ↦ False.elim (hi h)⟩
  choose c hc using hex
  refine ⟨c, fun i ↦ (hc i).1, ?_, ?_⟩
  · exact hdata.mono fun i hi ↦ (hc i).2 hi
  · have hlim' : Tendsto (fun i ↦ (4 / 3 : ℝ) * L * ε i) l (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hlim
    apply Metric.tendstoUniformly_iff.2
    intro δ hδ
    filter_upwards [hdata, hlim'.eventually (gt_mem_nhds hδ)] with i hi hlt q
    rw [dist_zero_left]
    exact (((hc i).2 hi).1 q).2.1.trans_lt hlt

#print axioms uniform_correction_family

end GlobalEmbedding.Paper
