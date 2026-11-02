import GlobalEmbedding.Paper.InducedMetric
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Vanishing normalized defects give the actual limiting metric

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `thm:repair`,
lines 776–778; DAG node `repair-finite-wait-convergence`.

This file uses the original tangent bilinear form `GlobalEmbedding.Paper.inducedMetric`
and the actual native ambient differential `mvfderiv`. It introduces no replacement
metric or differential data. Convergence of the actual differential, a vanishing
scalar defect scale, and eventual bounds on the actual normalized defect imply the
exact metric identity for the same limit map.

The preceding coordinate-series result still needs its chart-to-manifold adapter
to establish the differential-convergence hypothesis here. Smoothness and retained
phase margins are separate obligations, not consequences claimed in this file.
-/

open Manifold Filter
open scoped Topology ContDiff RealInnerProductSpace

namespace GlobalEmbedding.Offline

open GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}

/-- The original induced metric is exactly the inner product of the two native
ambient derivatives. This only exposes the target-tangent identification already
present in the original definition. -/
theorem inducedMetric_apply_mvfderiv
    (F : M → EuclideanSpace ℝ (Fin N)) (x : M) (v w : TangentSpace I x) :
    inducedMetric (I := I) F x v w = ⟪mvfderiv I F x v, mvfderiv I F x w⟫ := rfl

/-- Pointwise convergence of actual differentials implies convergence of the
original induced metric evaluated on every actual pair of tangent vectors.

Source: `thm:repair`, line 776. Apply continuity of the Euclidean inner product to
the two converging derivative values, using the original metric formula. -/
theorem inducedMetric_tendsto_of_mvfderiv
    (Fseq : ℕ → M → EuclideanSpace ℝ (Fin N))
    (F : M → EuclideanSpace ℝ (Fin N))
    (hD : ∀ (x : M) (v : TangentSpace I x),
      Tendsto (fun n ↦ mvfderiv I (Fseq n) x v) atTop (𝓝 (mvfderiv I F x v)))
    (x : M) (v w : TangentSpace I x) :
    Tendsto (fun n ↦ inducedMetric (I := I) (Fseq n) x v w) atTop
      (𝓝 (inducedMetric (I := I) F x v w)) := by
  simpa only [inducedMetric_apply_mvfderiv] using (hD x v).inner (hD x w)

/-- The bounded normalized defect tends to zero and forces the exact metric
identity for the same limiting map.

Source: `thm:repair`, line 776; DAG `repair-finite-wait-convergence`.
Evaluate the actual bilinear identity on `v,w`. The factor `delta²` tends to zero,
and the real normalized-defect evaluations are eventually bounded, so their
product tends to zero. The actual metric evaluations also converge, by continuity
of the inner product. Uniqueness of the real limit gives equality on every tangent
pair, hence equality of the full original bilinear forms.

No bound uniform in `x,v,w` is needed for this final exact-identity step. The
geometric construction remains responsible for producing the stated differential
convergence and normalized-defect bounds. -/
theorem inducedMetric_eq_of_tendsto_normalized_defect
    (Fseq : ℕ → M → EuclideanSpace ℝ (Fin N))
    (F : M → EuclideanSpace ℝ (Fin N))
    (g : ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (Hseq : ℕ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (delta : ℕ → ℝ)
    (hD : ∀ (x : M) (v : TangentSpace I x),
      Tendsto (fun n ↦ mvfderiv I (Fseq n) x v) atTop (𝓝 (mvfderiv I F x v)))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      ∃ C : ℝ, ∀ᶠ n in atTop, ‖Hseq n x v w‖ ≤ C)
    (hdefect : ∀ n x, g x - inducedMetric (I := I) (Fseq n) x =
      delta n ^ 2 • Hseq n x) :
    inducedMetric (I := I) F = g := by
  funext x
  ext v w
  obtain ⟨C, hC⟩ := hH x v w
  have hdelta2 : Tendsto (fun n ↦ delta n ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using hdelta.pow 2
  have hnormalized : IsBoundedUnder (· ≤ ·) atTop
      (fun n ↦ ‖Hseq n x v w‖) := ⟨C, hC⟩
  have hproduct : Tendsto (fun n ↦ delta n ^ 2 * Hseq n x v w) atTop (𝓝 0) := by
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def] using
      NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hdelta2 hnormalized
  have heval (n : ℕ) : g x v w - inducedMetric (I := I) (Fseq n) x v w =
      delta n ^ 2 * Hseq n x v w := by
    have h := congrArg (fun B : LinearMap.BilinForm ℝ (TangentSpace I x) ↦ B v w)
      (hdefect n x)
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] using h
  have hzero : Tendsto
      (fun n ↦ g x v w - inducedMetric (I := I) (Fseq n) x v w) atTop (𝓝 0) := by
    simpa only [heval] using hproduct
  have hmetric := inducedMetric_tendsto_of_mvfderiv Fseq F hD x v w
  have hlimit : g x v w - inducedMetric (I := I) F x v w = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.sub hmetric) hzero
  exact (sub_eq_zero.mp hlimit).symm

/-- Operator-norm convergence of the actual ambient differential is sufficient
for the same exact-metric conclusion.

Source: `thm:repair`, line 776. Evaluation on a fixed tangent vector is continuous
for the native space of continuous linear maps. Specialize the preceding theorem
after this evaluation; no artificial metric carrier is introduced. -/
theorem inducedMetric_eq_of_tendsto_mvfderiv
    (Fseq : ℕ → M → EuclideanSpace ℝ (Fin N))
    (F : M → EuclideanSpace ℝ (Fin N))
    (g : ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (Hseq : ℕ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (delta : ℕ → ℝ)
    (hD : ∀ x : M,
      Tendsto (fun n ↦ mvfderiv I (Fseq n) x) atTop (𝓝 (mvfderiv I F x)))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      ∃ C : ℝ, ∀ᶠ n in atTop, ‖Hseq n x v w‖ ≤ C)
    (hdefect : ∀ n x, g x - inducedMetric (I := I) (Fseq n) x =
      delta n ^ 2 • Hseq n x) :
    inducedMetric (I := I) F = g := by
  apply inducedMetric_eq_of_tendsto_normalized_defect Fseq F g Hseq delta
    (hdelta := hdelta) (hH := hH) (hdefect := hdefect)
  intro x v
  exact ((continuous_eval_const v).tendsto (mvfderiv I F x)).comp (hD x)

/-- Parameter families retain source-only metric differentiation in the limit.

Source: `thm:repair`, lines 776–778. Apply the actual-metric limit theorem at each
fixed parameter value. The parameter type is arbitrary: this last passage requires
no extra compactness or regularity assumptions beyond those used earlier to produce
the common sequence and its stated estimates. -/
theorem inducedMetric_eq_of_tendsto_normalized_defect_family
    {P : Type*}
    (Fseq : ℕ → P → M → EuclideanSpace ℝ (Fin N))
    (F : P → M → EuclideanSpace ℝ (Fin N))
    (g : P → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (Hseq : ℕ → P → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (delta : ℕ → ℝ)
    (hD : ∀ (p : P) (x : M) (v : TangentSpace I x),
      Tendsto (fun n ↦ mvfderiv I (Fseq n p) x v) atTop (𝓝 (mvfderiv I (F p) x v)))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hH : ∀ (p : P) (x : M) (v w : TangentSpace I x),
      ∃ C : ℝ, ∀ᶠ n in atTop, ‖Hseq n p x v w‖ ≤ C)
    (hdefect : ∀ n p x, g p x - inducedMetric (I := I) (Fseq n p) x =
      delta n ^ 2 • Hseq n p x) :
    ∀ p, inducedMetric (I := I) (F p) = g p := by
  intro p
  exact inducedMetric_eq_of_tendsto_normalized_defect
    (fun n ↦ Fseq n p) (F p) (g p) (fun n ↦ Hseq n p) delta
    (hD p) hdelta (hH p) (fun n x ↦ hdefect n p x)

#print axioms inducedMetric_apply_mvfderiv
#print axioms inducedMetric_tendsto_of_mvfderiv
#print axioms inducedMetric_eq_of_tendsto_normalized_defect
#print axioms inducedMetric_eq_of_tendsto_mvfderiv
#print axioms inducedMetric_eq_of_tendsto_normalized_defect_family

end GlobalEmbedding.Offline
