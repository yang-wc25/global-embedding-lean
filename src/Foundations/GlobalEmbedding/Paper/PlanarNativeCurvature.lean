import GlobalEmbedding.Paper.PlanarPeriodOneCalculus
import GlobalEmbedding.Paper.PlanarCurvatureSigns
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Curvature of the actual common period-one orbit derivative

Source: `main.tex`, `lem:planar`, lines 252–265.
DAG: `planar-native-curvature`.
The curvature is the original Euclidean inner product of the quarter-turned
actual velocity with the actual iterated orbit derivative. The real profile
result is applied to each actual orbit; no desired sign is supplied.
-/

noncomputable section
open scoped Manifold ContDiff InnerProductSpace

namespace GlobalEmbedding.Paper

/-- The true signed curvature of the actual common orbit derivative. -/
def planarOrbitCurvature {M : Type*} (R : ℝ → M → M) (f : M → Planar) (x : M) : ℝ :=
  ⟪planarQuarterTurn (orbitDeriv R f x), orbitDeriv R (orbitDeriv R f) x⟫_ℝ

/-- The original Euclidean curvature inner product is the actual determinant. -/
theorem planarOrbitCurvature_coordinates {M : Type*}
    (R : ℝ → M → M) (f : M → Planar) (x : M) :
    planarOrbitCurvature R f x =
      orbitDeriv R f x 0 * orbitDeriv R (orbitDeriv R f) x 1 -
        orbitDeriv R f x 1 * orbitDeriv R (orbitDeriv R f) x 0 := by
  simp [planarOrbitCurvature, planarQuarterTurn,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring

/-- Taking an actual Euclidean coordinate commutes with differentiating the
actual orbit map, at its actual translated time. -/
theorem planarOrbitCoordinate_hasDerivAt {M : Type*}
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (f : M → Planar) (hf : ∀ x, Differentiable ℝ (fun s ↦ f (R s x)))
    (x : M) (t : ℝ) (i : Fin 2) :
    HasDerivAt (fun s ↦ f (R s x) i) (orbitDeriv R f (R t x) i) t := by
  have hd := (hf x t).hasDerivAt
  rw [← orbitDeriv_flow R hR f t x] at hd
  exact (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).hasFDerivAt.comp_hasDerivAt t hd

/-- The actual scalar second derivative is a coordinate of the actual iterated
common orbit derivative, with no alternative vector field or formal jet. -/
theorem planarOrbitCoordinate_second_deriv {M : Type*}
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (f : M → Planar) (hf : ∀ x, Differentiable ℝ (fun s ↦ f (R s x)))
    (hv : ∀ x, Differentiable ℝ (fun s ↦ orbitDeriv R f (R s x)))
    (x : M) (t : ℝ) (i : Fin 2) :
    deriv (deriv (fun s ↦ f (R s x) i)) t =
      orbitDeriv R (orbitDeriv R f) (R t x) i := by
  have hd : deriv (fun s ↦ f (R s x) i) =
      fun s ↦ orbitDeriv R f (R s x) i := by
    funext s
    exact (planarOrbitCoordinate_hasDerivAt R hR f hf x s i).deriv
  rw [hd]
  exact (planarOrbitCoordinate_hasDerivAt R hR (orbitDeriv R f) hv x t i).deriv

/-- Actual curvature restricted to each actual orbit equals the scalar
curvature of its two actual coordinate profiles. -/
theorem planarOrbitCurvature_on_orbit {M : Type*}
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (f : M → Planar) (hf : ∀ x, Differentiable ℝ (fun s ↦ f (R s x)))
    (hv : ∀ x, Differentiable ℝ (fun s ↦ orbitDeriv R f (R s x)))
    (x : M) (t : ℝ) :
    planarSignedCurvature (fun s ↦ f (R s x) 0) (fun s ↦ f (R s x) 1) t =
      planarOrbitCurvature R f (R t x) := by
  rw [planarSignedCurvature,
    (planarOrbitCoordinate_hasDerivAt R hR f hf x t 0).deriv,
    (planarOrbitCoordinate_hasDerivAt R hR f hf x t 1).deriv,
    planarOrbitCoordinate_second_deriv R hR f hf hv x t 0,
    planarOrbitCoordinate_second_deriv R hR f hf hv x t 1,
    planarOrbitCurvature_coordinates]

/-- Every actual orbit of the genuine unit-speed reflected map has both strict
curvature signs, for the original common orbit derivative. -/
theorem planarOrbitCurvature_both_signs {M : Type*}
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h1 : ∀ x, R 1 x = x)
    (f : M → Planar) (hf : ∀ x, Differentiable ℝ (fun s ↦ f (R s x)))
    (hv : ∀ x, Differentiable ℝ (fun s ↦ orbitDeriv R f (R s x)))
    (hunit : ∀ x, ‖orbitDeriv R f x‖ = 1)
    (hreflect : ∀ x, f (R (1 / 2) x) = planarReflection (f x)) (x : M) :
    (∃ t, 0 < planarOrbitCurvature R f (R t x)) ∧
      (∃ t, planarOrbitCurvature R f (R t x) < 0) := by
  have hcoord (i : Fin 2) : Differentiable ℝ (fun s ↦ f (R s x) i) :=
    fun s ↦ (planarOrbitCoordinate_hasDerivAt R hR f hf x s i).differentiableAt
  have hdcoord (i : Fin 2) : Differentiable ℝ (deriv (fun s ↦ f (R s x) i)) := by
    have he : deriv (fun s ↦ f (R s x) i) =
        fun s ↦ orbitDeriv R f (R s x) i := by
      funext s
      exact (planarOrbitCoordinate_hasDerivAt R hR f hf x s i).deriv
    rw [he]
    exact fun s ↦ (planarOrbitCoordinate_hasDerivAt R hR
      (orbitDeriv R f) hv x s i).differentiableAt
  have hu (s : ℝ) : deriv (fun t ↦ f (R t x) 0) s ^ 2 +
      deriv (fun t ↦ f (R t x) 1) s ^ 2 = 1 := by
    rw [(planarOrbitCoordinate_hasDerivAt R hR f hf x s 0).deriv,
      (planarOrbitCoordinate_hasDerivAt R hR f hf x s 1).deriv]
    have he := congrArg (fun r : ℝ ↦ r ^ 2) (hunit (R s x))
    simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, one_pow] using he
  have hr (s : ℝ) : f (R (s + 1 / 2) x) = planarReflection (f (R s x)) := by
    rw [add_comm s (1 / 2), hR, hreflect]
  have hp (i : Fin 2) := orbitMap_periodic R hR h1 (fun y ↦ f y i) x
  have hr0 (s : ℝ) : f (R (s + 1 / 2) x) 0 = f (R s x) 0 := by
    simpa only [planarReflection_apply_zero] using
      (congrArg (fun p : Planar ↦ p 0) (hr s))
  have hr1 (s : ℝ) : f (R (s + 1 / 2) x) 1 = -f (R s x) 1 := by
    simpa only [planarReflection_apply_one] using
      (congrArg (fun p : Planar ↦ p 1) (hr s))
  have hpositive := planar_curvature_both_signs
    (hcoord 0) (hcoord 1) (hdcoord 0) (hdcoord 1) (hp 0) (hp 1) hu
    hr0 hr1
  simpa only [planarOrbitCurvature_on_orbit R hR f hf hv x] using hpositive

/-- The actual iterated orbit derivative satisfies the original quarter-turn
curvature equation at each actual point. -/
theorem planarOrbitCurvature_acceleration {M : Type*}
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (hzero : ∀ x, R 0 x = x)
    (f : M → Planar) (hf : ∀ x, Differentiable ℝ (fun s ↦ f (R s x)))
    (hv : ∀ x, Differentiable ℝ (fun s ↦ orbitDeriv R f (R s x)))
    (hunit : ∀ x, ‖orbitDeriv R f x‖ = 1) (x : M) :
    orbitDeriv R (orbitDeriv R f) x =
      planarOrbitCurvature R f x • planarQuarterTurn (orbitDeriv R f x) := by
  have hdcoord (i : Fin 2) : Differentiable ℝ (deriv (fun s ↦ f (R s x) i)) := by
    have he : deriv (fun s ↦ f (R s x) i) =
        fun s ↦ orbitDeriv R f (R s x) i := by
      funext s
      exact (planarOrbitCoordinate_hasDerivAt R hR f hf x s i).deriv
    rw [he]
    exact fun s ↦ (planarOrbitCoordinate_hasDerivAt R hR
      (orbitDeriv R f) hv x s i).differentiableAt
  have hu (s : ℝ) : deriv (fun t ↦ f (R t x) 0) s ^ 2 +
      deriv (fun t ↦ f (R t x) 1) s ^ 2 = 1 := by
    rw [(planarOrbitCoordinate_hasDerivAt R hR f hf x s 0).deriv,
      (planarOrbitCoordinate_hasDerivAt R hR f hf x s 1).deriv]
    have he := congrArg (fun r : ℝ ↦ r ^ 2) (hunit (R s x))
    simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, one_pow] using he
  have ha := planar_acceleration_eq_curvature (hdcoord 0) (hdcoord 1) hu 0
  rw [planarOrbitCoordinate_second_deriv R hR f hf hv x 0 0,
    planarOrbitCoordinate_second_deriv R hR f hf hv x 0 1,
    planarOrbitCurvature_on_orbit R hR f hf hv x 0,
    (planarOrbitCoordinate_hasDerivAt R hR f hf x 0 0).deriv,
    (planarOrbitCoordinate_hasDerivAt R hR f hf x 0 1).deriv,
    hzero] at ha
  ext i
  fin_cases i
  · change orbitDeriv R (orbitDeriv R f) x 0 =
      planarOrbitCurvature R f x * -orbitDeriv R f x 1
    nlinarith [ha.1]
  · change orbitDeriv R (orbitDeriv R f) x 1 =
      planarOrbitCurvature R f x * orbitDeriv R f x 0
    exact ha.2

/-- The actual original curvature changes sign at the antipodal half-period. -/
theorem planarOrbitCurvature_half_odd {M : Type*}
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (hzero : ∀ x, R 0 x = x)
    (f : M → Planar) (hf : ∀ x, Differentiable ℝ (fun s ↦ f (R s x)))
    (hv : ∀ x, Differentiable ℝ (fun s ↦ orbitDeriv R f (R s x)))
    (hreflect : ∀ x, f (R (1 / 2) x) = planarReflection (f x)) (x : M) :
    planarOrbitCurvature R f (R (1 / 2) x) = -planarOrbitCurvature R f x := by
  have hr (s : ℝ) : f (R (s + 1 / 2) x) = planarReflection (f (R s x)) := by
    rw [add_comm s (1 / 2), hR, hreflect]
  have hr0 (s : ℝ) : f (R (s + 1 / 2) x) 0 = f (R s x) 0 := by
    simpa only [planarReflection_apply_zero] using
      (congrArg (fun p : Planar ↦ p 0) (hr s))
  have hr1 (s : ℝ) : f (R (s + 1 / 2) x) 1 = -f (R s x) 1 := by
    simpa only [planarReflection_apply_one] using
      (congrArg (fun p : Planar ↦ p 1) (hr s))
  have ho := planar_curvature_half_period_odd
    (f := fun s : ℝ ↦ f (R s x) 0) (g := fun s : ℝ ↦ f (R s x) 1) hr0 hr1 0
  simpa only [planarOrbitCurvature_on_orbit R hR f hf hv x, zero_add, hzero] using ho

section Smooth
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]

/-- Genuine smoothness of the actual derivative fields implies genuine native
smoothness of the original curvature, by the literal determinant identity. -/
theorem planarOrbitCurvature_contMDiff (R : ℝ → M → M) (f : M → Planar)
    (hv : ContMDiff I 𝓘(ℝ, Planar) ∞ (orbitDeriv R f))
    (ha : ContMDiff I 𝓘(ℝ, Planar) ∞ (orbitDeriv R (orbitDeriv R f))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (planarOrbitCurvature R f) := by
  have hv0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).contMDiff.comp hv
  have hv1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).contMDiff.comp hv
  have ha0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).contMDiff.comp ha
  have ha1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).contMDiff.comp ha
  have he : planarOrbitCurvature R f = fun x ↦
      orbitDeriv R f x 0 * orbitDeriv R (orbitDeriv R f) x 1 -
        orbitDeriv R f x 1 * orbitDeriv R (orbitDeriv R f) x 0 :=
    funext (planarOrbitCurvature_coordinates R f)
  rw [he]
  exact (hv0.mul ha1).sub (hv1.mul ha0)

end Smooth
end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.planarOrbitCurvature_both_signs
#print axioms GlobalEmbedding.Paper.planarOrbitCurvature_acceleration
#print axioms GlobalEmbedding.Paper.planarOrbitCurvature_half_odd
#print axioms GlobalEmbedding.Paper.planarOrbitCurvature_contMDiff
