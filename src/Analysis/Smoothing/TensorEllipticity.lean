import Smoothing.TensorParameterGain

/-!
# Ellipticity reserves for the actual signed tensor smoother

A signed kernel has no positivity property. Positivity is instead derived
from the proved actual coefficient C0 error and the original uniform positive
cone margin. All dimension and moving-frame costs are displayed.
-/

open Module MeasureTheory Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Continuation Function Set
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false

section FrameAlgebra

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The genuine Euclidean vector of coefficients of a tangent vector in a
chosen actual chart basis; no arbitrary norm on dependent fibers is inserted. -/
def tensorFrameVector (b : Basis (Fin n) ℝ V) (v : V) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => b.repr v i

@[simp] theorem tensorFrameVector_eq_zero_iff (b : Basis (Fin n) ℝ V) (v : V) :
    tensorFrameVector b v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply b.repr.injective
    ext i
    have hi := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w i) h
    change b.repr v i = 0 at hi
    simpa only [map_zero, Finsupp.zero_apply] using hi
  · intro h
    subst v
    simp only [tensorFrameVector, map_zero, Finsupp.zero_apply]
    rfl

theorem tensorFrameVector_component_le (b : Basis (Fin n) ℝ V) (v : V) (i : Fin n) :
    |b.repr v i| ≤ ‖tensorFrameVector b v‖ :=
  PiLp.norm_apply_le (tensorFrameVector b v) i

/-- Actual component error controls the actual quadratic error in the true
frame. The explicit n² factor works also in dimension zero. -/
theorem tensor_diagonal_error_le (b : Basis (Fin n) ℝ V)
    (H S : LinearMap.BilinForm ℝ V) (eps : ℝ) (heps : 0 ≤ eps)
    (herror : ‖tensorFrameComponents b (H - S)‖ ≤ eps) (v : V) :
    |H v v - S v v| ≤ (n : ℝ) ^ 2 * eps * ‖tensorFrameVector b v‖ ^ 2 := by
  have hentry (i j : Fin n) : |(H - S) (b i) (b j)| ≤ eps := by
    simpa only [tensorFrameComponents, Equiv.symm_apply_apply, Real.norm_eq_abs] using
      (norm_le_pi_norm (tensorFrameComponents b (H - S)) (finProdFinEquiv (i, j))).trans herror
  have hrep : H v v - S v v =
      ∑ i, ∑ j, b.repr v i * (H - S) (b i) (b j) * b.repr v j := by
    change ((H - S) v) v = _
    conv_lhs => rw [← Matrix.toBilin_toMatrix b (H - S)]
    rw [Matrix.toBilin_apply]
    simp only [LinearMap.BilinForm.toMatrix_apply]
  rw [hrep]
  calc
    |∑ i, ∑ j, b.repr v i * (H - S) (b i) (b j) * b.repr v j| ≤
        ∑ i, ∑ j, |b.repr v i * (H - S) (b i) (b j) * b.repr v j| := by
      have hs : |∑ i, ∑ j, b.repr v i * (H - S) (b i) (b j) * b.repr v j| ≤
          ∑ i, |∑ j, b.repr v i * (H - S) (b i) (b j) * b.repr v j| := by
        simpa only [Real.norm_eq_abs] using
          norm_sum_le Finset.univ (fun i : Fin n => ∑ j, b.repr v i * (H - S) (b i) (b j) * b.repr v j)
      apply hs.trans
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using
        norm_sum_le Finset.univ (fun j : Fin n => b.repr v i * (H - S) (b i) (b j) * b.repr v j)
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖tensorFrameVector b v‖ * eps * ‖tensorFrameVector b v‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (tensorFrameVector_component_le b v i) (hentry i j)
        (abs_nonneg _) (norm_nonneg _)) (tensorFrameVector_component_le b v j)
        (abs_nonneg _) (mul_nonneg (norm_nonneg _) heps)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- A genuine C0 coefficient reserve retains half the original uniform
ellipticity for the actual bilinear form, without positivity of any kernel. -/
theorem tensor_half_ellipticity (b : Basis (Fin n) ℝ V)
    (H S : LinearMap.BilinForm ℝ V) (alpha eps : ℝ) (heps : 0 ≤ eps)
    (hH : ∀ v, alpha * ‖tensorFrameVector b v‖ ^ 2 ≤ H v v)
    (herror : ‖tensorFrameComponents b (H - S)‖ ≤ eps)
    (hreserve : (n : ℝ) ^ 2 * eps ≤ alpha / 2) (v : V) :
    (alpha / 2) * ‖tensorFrameVector b v‖ ^ 2 ≤ S v v := by
  have he := tensor_diagonal_error_le b H S eps heps herror v
  have hle := (le_abs_self (H v v - S v v)).trans he
  have hr := mul_le_mul_of_nonneg_right hreserve (sq_nonneg ‖tensorFrameVector b v‖)
  have hh := hH v
  nlinarith

/-- Strict positive definiteness follows from the actual half-ellipticity
bound and injectivity of the true frame coordinates. -/
theorem tensor_positive_of_half_ellipticity (b : Basis (Fin n) ℝ V)
    (S : LinearMap.BilinForm ℝ V) (alpha : ℝ) (halpha : 0 < alpha)
    (hS : ∀ v, (alpha / 2) * ‖tensorFrameVector b v‖ ^ 2 ≤ S v v) :
    ∀ v ≠ 0, 0 < S v v := by
  intro v hv
  have hnorm : 0 < ‖tensorFrameVector b v‖ :=
    norm_pos_iff.mpr (fun h => hv ((tensorFrameVector_eq_zero_iff b v).mp h))
  exact (mul_pos (by positivity : 0 < alpha / 2) (sq_pos_of_pos hnorm)).trans_le (hS v)

end FrameAlgebra

section OriginalC0

variable {ι : Type*} [Fintype ι] {s q : ℕ}

/-- The frozen original cumulative C0 norm bounds every actual component
value on the true evaluation domain; no smoothness or finite-toReal shortcut. -/
theorem paperAtlasC0_value_le
    (f : ι → (Fin s → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin s → ℝ))
    (hfinite : paperAtlasCj 0 f O S ≠ ⊤) (i : ι) {y : Fin s → ℝ} (hy : y ∈ S i) :
    ‖f i y‖ ≤ (paperAtlasCj 0 f O S).toReal := by
  apply (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).mpr
  intro k
  have h : ENNReal.ofReal ‖f i y k‖ ≤ paperAtlasCj 0 f O S := by
    unfold paperAtlasCj paperCoordinateCj
    exact le_iSup_of_le i (le_iSup_of_le ⟨[], by simp⟩
      (le_iSup_of_le ⟨y, hy⟩ (le_iSup_of_le k le_rfl)))
  have hr := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfinite).mpr h
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using hr

end OriginalC0

end

end GlobalEmbedding.Offline
