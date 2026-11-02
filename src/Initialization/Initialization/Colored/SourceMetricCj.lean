import Initialization.Colored.SourceErrorJets
import Initialization.Colored.MetricError
import GlobalEmbedding.Paper.FrameGramCjEstimates

/-!
# The actual C^j induced-metric error of the same selected map

The actual derivative and the exact selector ideal derivative enter the already
verified Gram-operator estimate. The ideal Gram is proved equal to the genuine
coframe Gram. A separate identity identifies the operator coefficients with the
original native inducedMetric, rather than a separately specified metric field.
-/

noncomputable section
open Function Set Metric Manifold
open scoped ContDiff Topology Manifold

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Actual covector rows of an actual coframe operator. -/
def coframeRows {n : ℕ} (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : E) (l : Fin n) : E →L[ℝ] ℝ := (EuclideanSpace.proj l).comp (c x)

@[simp] theorem coframeRows_apply {n : ℕ}
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) (x v : E) (l : Fin n) :
    coframeRows c x l v = (c x v) l := rfl

theorem coframeRows_contDiffOn {n : ℕ}
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) (O : Set E)
    (hc : ContDiffOn ℝ ∞ c O) (l : Fin n) :
    ContDiffOn ℝ ∞ (fun x ↦ coframeRows c x l) O :=
  contDiffOn_const.clm_comp hc

/-- The coframe-transformed ideal derivative is exactly the same selector Gram
frame, with no independently chosen isometry. -/
theorem selectorSourceIdealFirst_eq_gramFrame {n C : ℕ}
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (z : E → FreeHopfProduct (fun _ : Fin n ↦ C))
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) (x : E) :
    selectorSourceIdealFirst (fun _ : Fin n ↦ C) S z (coframeRows c) x =
      (gramFrame (fun l ↦ freeHopfDeriv (fun _ : Fin n ↦ C) l S (z x))).comp (c x) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [selectorSourceIdealFirst, sum_apply, ContinuousLinearMap.smulRight_apply,
    coframeRows_apply, ContinuousLinearMap.comp_apply, gramFrame_apply]

/-- The actual Gram operator of a genuine linear map. -/
def actualGramOperator (A : E →L[ℝ] F) : E →L[ℝ] E := A.adjoint.comp A

/-- Native induced-metric coordinate coefficients, represented by the exact
Euclidean Gram operator of the actual derivative. -/
def actualMetricOperator (H : E → F) (x : E) : E →L[ℝ] E :=
  actualGramOperator (fderiv ℝ H x)

theorem actualMetricOperator_inner (H : E → F) (x v w : E) :
    inner ℝ (actualMetricOperator H x v) w =
      inner ℝ (fderiv ℝ H x v) (fderiv ℝ H x w) :=
  (fderiv ℝ H x).adjoint_inner_left w (fderiv ℝ H x v)

/-- These are the original native inducedMetric coefficients, with the actual
tangent-space casts used by its definition. -/
theorem actualMetricOperator_inducedMetric {N : ℕ}
    (H : E → EuclideanSpace ℝ (Fin N)) (x v w : E) :
    inner ℝ (actualMetricOperator H x v) w =
      inducedMetric (I := 𝓘(ℝ, E)) H x
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm v)
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm w) := by
  rw [actualMetricOperator_inner, inducedMetric_apply, mfderiv_eq_fderiv]
  rfl

/-- Exact ideal Gram identity for the actual coframe field. -/
theorem selectorSourceIdealFirst_gramOperator {n C : ℕ}
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (hGram : ∀ z, Matrix.gram ℝ (fun l ↦ freeHopfDeriv (fun _ : Fin n ↦ C) l S z) = 1)
    (z : E → FreeHopfProduct (fun _ : Fin n ↦ C))
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) (x : E) :
    actualGramOperator (selectorSourceIdealFirst (fun _ : Fin n ↦ C) S z (coframeRows c) x) =
      actualGramOperator (c x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  simp only [actualGramOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, selectorSourceIdealFirst_eq_gramFrame]
  exact gramFrame_inner _ (hGram (z x)) (c x v) (c x w)

/-- C^j metric smallness for the actual selected map, using the native finite
derivative-supremum norm. The discrepancy is exactly DH minus the actual selector
ideal first jet, whose Gram is the coframe metric. -/
theorem selectorSource_metric_cj_bound {n C : ℕ} [Fact (0 < C)]
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ C)) 𝓘(ℝ, F) ∞ S)
    (hGram : ∀ z, Matrix.gram ℝ (fun l ↦ freeHopfDeriv (fun _ : Fin n ↦ C) l S z) = 1)
    (z : E → FreeHopfProduct (fun _ : Fin n ↦ C))
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n))
    (j : ℕ) (O : Set E) (hO : IsOpen O)
    (hZ : ContDiffOn ℝ ∞ (selectorSourceAmbient (fun _ : Fin n ↦ C) z) O)
    (hc : ContDiffOn ℝ ∞ c O)
    (L D δ : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hactual : ∀ k ≤ j, ∀ x ∈ O, ‖iteratedFDeriv ℝ k (fderiv ℝ (S ∘ z)) x‖ ≤ L)
    (hideal : ∀ k ≤ j, ∀ x ∈ O,
      ‖iteratedFDeriv ℝ k (selectorSourceIdealFirst (fun _ : Fin n ↦ C) S z (coframeRows c)) x‖ ≤ L)
    (herror : finiteCjNorm j
      (selectorSourceFirstError (fun _ : Fin n ↦ C) S z (coframeRows c)) O ≤ D * δ) :
    finiteCjNorm j
      (fun x ↦ actualMetricOperator (S ∘ z) x - actualGramOperator (c x)) O ≤
        ((j+1 : ℝ) * (2 * 2 ^ j * L) * D) * δ := by
  let A := fderiv ℝ (S ∘ z)
  let B := selectorSourceIdealFirst (fun _ : Fin n ↦ C) S z (coframeRows c)
  have hH : ContDiffOn ℝ ∞ (S ∘ z) O := by
    intro x hx
    exact (selectorSource_contDiffAt (fun _ : Fin n ↦ C) S hS z
      (hZ.contDiffAt (hO.mem_nhds hx))).contDiffWithinAt
  have hA : ContDiffOn ℝ ∞ A O :=
    hH.fderiv_of_isOpen hO (by simp : ∞ + 1 ≤ (∞ : ℕ∞ω))
  have hB : ContDiffOn ℝ ∞ B O := by
    intro x hx
    exact (selectorSourceIdealFirst_contDiffAt (fun _ : Fin n ↦ C) S hS z (coframeRows c)
      (hZ.contDiffAt (hO.mem_nhds hx))
      (fun l ↦ (coframeRows_contDiffOn c O hc l).contDiffAt (hO.mem_nhds hx))).contDiffWithinAt
  have h := frame_gram_cj_estimates j O hO A B hA hB L hL hactual hideal
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hbound⟩
  have heq : (fun x ↦ (A x).adjoint.comp (A x)) -
      (fun x ↦ (B x).adjoint.comp (B x)) =
      (fun x ↦ actualMetricOperator (S ∘ z) x - actualGramOperator (c x)) := by
    funext x
    change actualMetricOperator (S ∘ z) x - actualGramOperator (B x) = _
    rw [selectorSourceIdealFirst_gramOperator S hGram z c]
  rw [heq] at hbound
  have he : A - B = selectorSourceFirstError (fun _ : Fin n ↦ C) S z (coframeRows c) := rfl
  rw [he] at hbound
  exact hbound.trans ((mul_le_mul_of_nonneg_left herror (by positivity)).trans_eq (by ring))

end GlobalEmbedding.Initialization
