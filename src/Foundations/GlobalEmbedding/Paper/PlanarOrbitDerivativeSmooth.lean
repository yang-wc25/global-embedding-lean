import GlobalEmbedding.Paper.PlanarPeriodOneCalculus
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Native smoothness of actual orbit derivatives

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines 262–266.
The native parameter-derivative theorem is applied to the actual time variable of the
jointly smooth orbit map. No formal vector field or derivative regularity is supplied.
-/

noncomputable section

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A genuine smooth family of real curves has a native smooth actual derivative at zero.
This is the existing native parameter-derivative theorem in normed time and target charts. -/
theorem contMDiff_parametric_deriv_zero (G : M × ℝ → F)
    (hG : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ G) :
    ContMDiff I 𝓘(ℝ, F) ∞ (fun x ↦ deriv (fun t : ℝ ↦ G (x, t)) 0) := by
  intro x
  have hd := (hG (x, 0)).mfderiv (fun x t ↦ G (x, t)) (fun _ : M ↦ (0 : ℝ))
    (contMDiffAt_const : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun _ : M ↦ (0 : ℝ)) x)
    (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp)
  have heq : inTangentCoordinates 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun _ : M ↦ (0 : ℝ))
      (fun y ↦ G (y, 0))
      (fun y ↦ mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun t : ℝ ↦ G (y, t)) 0) x =
      (fun y ↦ fderiv ℝ (fun t : ℝ ↦ G (y, t)) 0) := by
    funext y
    rw [inTangentCoordinates_eq_mfderiv_comp (by simp) (by simp)]
    simp only [mfld_simps, mvfderiv, mfderiv_eq_fderiv, mfderivWithin_eq_fderivWithin,
      fderivWithin_univ, fderiv_id]
    ext
    rfl
  rw [heq] at hd
  have hc := hd.clm_apply
    (contMDiffAt_const : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun _ : M ↦ (1 : ℝ)) x)
  exact hc

/-- The actual derivative of a smooth observable along a jointly native smooth flow is
native smooth. The input is the real action itself, not an independently specified operator. -/
theorem contMDiff_orbitDeriv (R : ℝ → M → M)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ R p.1 p.2))
    (f : M → F) (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) :
    ContMDiff I 𝓘(ℝ, F) ∞ (orbitDeriv R f) := by
  apply contMDiff_parametric_deriv_zero (fun p : M × ℝ ↦ f (R p.2 p.1))
  exact hf.comp (hR.comp (contMDiff_snd.prodMk contMDiff_fst))

/-- Every finite iteration of the actual orbit derivative remains native smooth.
Iteration uses the same genuine derivative operation at each step. -/
theorem contMDiff_iterate_orbitDeriv (R : ℝ → M → M)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ R p.1 p.2))
    (f : M → F) (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (k : ℕ) :
    ContMDiff I 𝓘(ℝ, F) ∞ ((orbitDeriv R)^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact contMDiff_orbitDeriv R hR _ ih

omit [IsManifold I ∞ M] in
/-- The smooth native observable has the actual one-variable derivative at every orbit time,
equal to the same native orbit derivative at the translated starting point. -/
theorem hasDerivAt_orbit (R : ℝ → M → M)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ R p.1 p.2))
    (hadd : ∀ s t x, R (s + t) x = R s (R t x))
    (f : M → F) (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (t : ℝ) (x : M) :
    HasDerivAt (fun s : ℝ ↦ f (R s x)) (orbitDeriv R f (R t x)) t := by
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ∞ (fun s : ℝ ↦ f (R s x)) :=
    hf.comp (hR.comp (contMDiff_id.prodMk contMDiff_const))
  rw [orbitDeriv_flow R hadd f t x]
  exact (hc.contDiff.differentiable (by simp) t).hasDerivAt

/-- Every iterated native orbit derivative gives the actual next derivative along each orbit. -/
theorem hasDerivAt_iterate_orbitDeriv (R : ℝ → M → M)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ R p.1 p.2))
    (hadd : ∀ s t x, R (s + t) x = R s (R t x))
    (f : M → F) (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (k : ℕ) (t : ℝ) (x : M) :
    HasDerivAt (fun s : ℝ ↦ ((orbitDeriv R)^[k] f) (R s x))
      (((orbitDeriv R)^[k + 1] f) (R t x)) t := by
  rw [Function.iterate_succ_apply']
  exact hasDerivAt_orbit R hR hadd _ (contMDiff_iterate_orbitDeriv R hR f hf k) t x

#print axioms contMDiff_parametric_deriv_zero
#print axioms contMDiff_orbitDeriv
#print axioms contMDiff_iterate_orbitDeriv
#print axioms hasDerivAt_orbit
#print axioms hasDerivAt_iterate_orbitDeriv

end GlobalEmbedding.Paper
