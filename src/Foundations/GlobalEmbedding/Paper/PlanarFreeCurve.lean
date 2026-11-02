import GlobalEmbedding.Paper.PlanarPeriodOneCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# The actual free paraboloid lift of a unit-speed planar selector

Source: `main.tex`, `lem:planar`, line 265.
DAG: `planar-free-curve`. All jets are computed from the actual input functions.
No curvature nonvanishing is needed: the height acceleration contributes one
even at a zero of the actual planar curvature.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The true map `(p, |p|²/2)` in the original Euclidean dimension three. -/
def planarQuadraticLift (p : Planar) : SpaceCurve :=
  WithLp.toLp 2 ![p 0, p 1, (p 0 ^ 2 + p 1 ^ 2) / 2]

/-- The last coordinate is literally half the original Euclidean squared norm. -/
theorem planarQuadraticLift_last (p : Planar) :
    planarQuadraticLift p 2 = ‖p‖ ^ 2 / 2 := by
  simp [planarQuadraticLift, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- The actual first jet of the paraboloid lift. -/
def planarLiftVelocity (p v : Planar) : SpaceCurve :=
  WithLp.toLp 2 ![v 0, v 1, p 0 * v 0 + p 1 * v 1]

/-- The actual second jet, retaining the actual squared-speed term. -/
def planarLiftAcceleration (p v a : Planar) : SpaceCurve :=
  WithLp.toLp 2 ![a 0, a 1,
    v 0 ^ 2 + v 1 ^ 2 + p 0 * a 0 + p 1 * a 1]

/-- The actual ordinary derivative of the actual paraboloid map. -/
theorem planarQuadraticLift_hasDerivAt {f : ℝ → Planar} {v : Planar} {t : ℝ}
    (hf : HasDerivAt f v t) :
    HasDerivAt (fun s ↦ planarQuadraticLift (f s)) (planarLiftVelocity (f t) v) t := by
  have h0 : HasDerivAt (fun s ↦ f s 0) (v 0) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).hasFDerivAt.comp_hasDerivAt t hf
  have h1 : HasDerivAt (fun s ↦ f s 1) (v 1) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).hasFDerivAt.comp_hasDerivAt t hf
  have hh : HasDerivAt (fun s ↦ (f s 0 ^ 2 + f s 1 ^ 2) / 2)
      (f t 0 * v 0 + f t 1 * v 1) t := by
    convert ((h0.pow 2).add (h1.pow 2)).div_const 2 using 1; ring
  have hpi : HasDerivAt
      (fun s ↦ ![f s 0, f s 1, (f s 0 ^ 2 + f s 1 ^ 2) / 2])
      ![v 0, v 1, f t 0 * v 0 + f t 1 * v 1] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact hh
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt t hpi

/-- Differentiate the actual first jet to obtain the actual second jet. -/
theorem planarLiftVelocity_hasDerivAt {f v : ℝ → Planar} {a : Planar} {t : ℝ}
    (hf : HasDerivAt f (v t) t) (hv : HasDerivAt v a t) :
    HasDerivAt (fun s ↦ planarLiftVelocity (f s) (v s))
      (planarLiftAcceleration (f t) (v t) a) t := by
  have hf0 : HasDerivAt (fun s ↦ f s 0) (v t 0) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).hasFDerivAt.comp_hasDerivAt t hf
  have hf1 : HasDerivAt (fun s ↦ f s 1) (v t 1) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).hasFDerivAt.comp_hasDerivAt t hf
  have hv0 : HasDerivAt (fun s ↦ v s 0) (a 0) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).hasFDerivAt.comp_hasDerivAt t hv
  have hv1 : HasDerivAt (fun s ↦ v s 1) (a 1) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).hasFDerivAt.comp_hasDerivAt t hv
  have hh : HasDerivAt (fun s ↦ f s 0 * v s 0 + f s 1 * v s 1)
      (v t 0 ^ 2 + v t 1 ^ 2 + f t 0 * a 0 + f t 1 * a 1) t := by
    convert (hf0.mul hv0).add (hf1.mul hv1) using 1; ring
  have hpi : HasDerivAt
      (fun s ↦ ![v s 0, v s 1, f s 0 * v s 0 + f s 1 * v s 1])
      ![a 0, a 1, v t 0 ^ 2 + v t 1 ^ 2 + f t 0 * a 0 + f t 1 * a 1] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hv0
    · exact hv1
    · exact hh
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt t hpi

/-- The actual paraboloid first and second jets are independent, including at
zero planar acceleration. Unit speed and its differentiated identity suffice. -/
theorem planarLift_jets_independent (p v a : Planar)
    (hunit : v 0 ^ 2 + v 1 ^ 2 = 1)
    (horth : v 0 * a 0 + v 1 * a 1 = 0) :
    LinearIndependent ℝ ![planarLiftVelocity p v, planarLiftAcceleration p v a] := by
  rw [LinearIndependent.pair_iff]
  intro r s he
  have h0 := congrArg (fun w : SpaceCurve ↦ w 0) he
  have h1 := congrArg (fun w : SpaceCurve ↦ w 1) he
  have h2 := congrArg (fun w : SpaceCurve ↦ w 2) he
  change r * v 0 + s * a 0 = 0 at h0
  change r * v 1 + s * a 1 = 0 at h1
  change r * (p 0 * v 0 + p 1 * v 1) +
    s * (v 0 ^ 2 + v 1 ^ 2 + p 0 * a 0 + p 1 * a 1) = 0 at h2
  have hr : r = 0 := by
    nlinarith [congrArg (fun z : ℝ ↦ r * z) hunit,
      congrArg (fun z : ℝ ↦ s * z) horth,
      congrArg (fun z : ℝ ↦ v 0 * z) h0,
      congrArg (fun z : ℝ ↦ v 1 * z) h1]
  refine ⟨hr, ?_⟩
  rw [hr, zero_mul, zero_add] at h0 h1 h2
  rw [hunit] at h2
  nlinarith [congrArg (fun z : ℝ ↦ p 0 * z) h0,
    congrArg (fun z : ℝ ↦ p 1 * z) h1]

/-- The actual first and second derivatives of the actual lifted curve are
independent at every time. The supplied jets are identified with derivatives
by `HasDerivAt`; differentiated actual unit speed proves orthogonality. -/
theorem planarQuadraticLift_free
    {f v a : ℝ → Planar} (hf : ∀ t, HasDerivAt f (v t) t)
    (hv : ∀ t, HasDerivAt v (a t) t) (hunit : ∀ t, ‖v t‖ = 1) (t : ℝ) :
    LinearIndependent ℝ ![deriv (fun s ↦ planarQuadraticLift (f s)) t,
      deriv (deriv (fun s ↦ planarQuadraticLift (f s))) t] := by
  have hfirst : deriv (fun s ↦ planarQuadraticLift (f s)) =
      fun s ↦ planarLiftVelocity (f s) (v s) := by
    funext s
    exact (planarQuadraticLift_hasDerivAt (hf s)).deriv
  have hsecond := (planarLiftVelocity_hasDerivAt (hf t) (hv t)).deriv
  have hnorm (s : ℝ) : v s 0 ^ 2 + v s 1 ^ 2 = 1 := by
    have hn := congrArg (fun z : ℝ ↦ z ^ 2) (hunit s)
    simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, one_pow] using hn
  have h0 : HasDerivAt (fun s ↦ v s 0) (a t 0) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).hasFDerivAt.comp_hasDerivAt t (hv t)
  have h1 : HasDerivAt (fun s ↦ v s 1) (a t 1) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).hasFDerivAt.comp_hasDerivAt t (hv t)
  have hd := ((h0.pow 2).add (h1.pow 2)).deriv
  change deriv (fun s ↦ v s 0 ^ 2 + v s 1 ^ 2) t = _ at hd
  rw [show (fun s ↦ v s 0 ^ 2 + v s 1 ^ 2) = fun _ ↦ (1 : ℝ) from
    funext hnorm, deriv_const] at hd
  norm_num at hd
  have horth : v t 0 * a t 0 + v t 1 * a t 1 = 0 := by linarith
  rw [hfirst, hsecond]
  exact planarLift_jets_independent (f t) (v t) (a t) (hnorm t) horth

/-- Any invertible triangular change of the actual two jets preserves freeness.
This also covers the orbit-invariant outer scale in intrinsic normalization. -/
theorem free_jets_triangular {V : Type*} [AddCommGroup V] [Module ℝ V]
    {u v : V} (hfree : LinearIndependent ℝ ![u, v])
    {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (μ : ℝ) :
    LinearIndependent ℝ ![α • u, β • v + μ • u] := by
  rw [LinearIndependent.pair_iff] at hfree ⊢
  intro r s he
  have ht : (r * α + s * μ) • u + (s * β) • v = 0 := by
    calc
      _ = r • (α • u) + s • (β • v + μ • u) := by
        simp only [add_smul, mul_smul, smul_add]
        abel
      _ = 0 := he
  obtain ⟨hfirst, hsecond⟩ := hfree _ _ ht
  have hs : s = 0 := (mul_eq_zero.mp hsecond).resolve_right hβ
  refine ⟨?_, hs⟩
  rw [hs, zero_mul, add_zero] at hfirst
  exact (mul_eq_zero.mp hfirst).resolve_right hα

/-- A genuine change of orbit parameter with nonzero speed preserves freeness. -/
theorem free_jets_reparametrize {V : Type*} [AddCommGroup V] [Module ℝ V]
    {u v : V} (hfree : LinearIndependent ℝ ![u, v])
    {α : ℝ} (hα : α ≠ 0) (μ : ℝ) :
    LinearIndependent ℝ ![α • u, α ^ 2 • v + μ • u] :=
  free_jets_triangular hfree hα (pow_ne_zero _ hα) μ

section Smooth
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]

/-- The actual paraboloid lift is globally native smooth. -/
theorem planarQuadraticLift_contMDiff {f : M → Planar}
    (hf : ContMDiff I 𝓘(ℝ, Planar) ∞ f) :
    ContMDiff I 𝓘(ℝ, SpaceCurve) ∞ (fun x ↦ planarQuadraticLift (f x)) := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).contMDiff.comp hf
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).contMDiff.comp hf
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contMDiff.comp
  apply contMDiff_pi_module_iff.mpr
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · simpa [pow_two] using ((h0.mul h0).add (h1.mul h1)).div_const 2

end Smooth
end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.planarQuadraticLift_hasDerivAt
#print axioms GlobalEmbedding.Paper.planarLiftVelocity_hasDerivAt
#print axioms GlobalEmbedding.Paper.planarLift_jets_independent
#print axioms GlobalEmbedding.Paper.planarQuadraticLift_free
#print axioms GlobalEmbedding.Paper.free_jets_triangular
#print axioms GlobalEmbedding.Paper.free_jets_reparametrize
#print axioms GlobalEmbedding.Paper.planarQuadraticLift_contMDiff
