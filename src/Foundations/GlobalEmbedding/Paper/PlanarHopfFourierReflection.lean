import GlobalEmbedding.Paper.PlanarOrbitFourier
import GlobalEmbedding.Paper.PlanarHopfFlow

/-!
# Actual antipodal Hopf Fourier approximation

Source: `literature/parallelizable-stable-plus-one/main.tex`, Lemma `lem:planar`, line262.
The genuine planar reflection is a real Euclidean linear isometric equivalence. The accepted
Fourier construction is applied to the actual native Hopf flow, retaining the source's literal
antipodal law and its actual period-one derivative.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The source's literal planar reflection, with its actual real linear and Euclidean
isometry data. It is its own inverse; no replacement of the planar norm is made. -/
def planarReflectionLinearIsometryEquiv : Planar ≃ₗᵢ[ℝ] Planar where
  toFun := planarReflection
  invFun := planarReflection
  left_inv v := by ext i; fin_cases i <;> simp [planarReflection]
  right_inv v := by ext i; fin_cases i <;> simp [planarReflection]
  map_add' u v := by ext i; fin_cases i <;> simp [planarReflection, add_comm]
  map_smul' a v := by ext i; fin_cases i <;> simp [planarReflection]
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, planarReflection]

/-- An actual smooth antipodally equivariant Hopf map with nowhere-zero actual orbit
derivative has an actual smooth orbit-analytic approximation with the same properties,
uniformly approximating both values and the actual orbit derivative by the requested error.
Apply the accepted full Fourier theorem with the genuine reflection and half-period law;
all flow, manifold, compactness and reflection linearity data are constructed here or in
the accepted actual Hopf modules, rather than supplied as additional hypotheses. -/
theorem planar_hopf_fourier_reflection
    (C : ℕ) [Fact (0 < C)] (g : PlanarHopfSphere C → Planar)
    (hg : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ g)
    (hreflect : ∀ z, g (-z) = planarReflection (g z))
    (hn : ∀ z, orbitDeriv planarHopfFlow g z ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : PlanarHopfSphere C → Planar,
      ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f ∧
      (∀ z, f (-z) = planarReflection (f z)) ∧
      (∀ z, orbitDeriv planarHopfFlow f z ≠ 0) ∧
      (∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) univ) ∧
      (∀ z, ‖f z - g z‖ < ε) ∧
      (∀ z, ‖orbitDeriv planarHopfFlow f z - orbitDeriv planarHopfFlow g z‖ < ε) := by
  have hhalf (z : PlanarHopfSphere C) :
      g (planarHopfFlow (1 / 2 : ℝ) z) =
        planarReflectionLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap (g z) := by
    rw [planarHopfFlow_half]
    exact hreflect z
  obtain ⟨p, hp, f, hf, hs, heq, hval, hder, ha, hnonzero⟩ :=
    planar_orbit_fourier_nonvanishing (planarHopfSmoothFlow C) g hg
      planarReflectionLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
      (1 / 2 : ℝ) hhalf hn ε hε
  refine ⟨f, hs, ?_, hnonzero, ha, hval, hder⟩
  intro z
  have hz := heq z
  change f (planarHopfFlow (1 / 2 : ℝ) z) = planarReflection (f z) at hz
  rwa [planarHopfFlow_half] at hz

#print axioms planarReflectionLinearIsometryEquiv
#print axioms planar_hopf_fourier_reflection

end GlobalEmbedding.Paper
