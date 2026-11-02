import GlobalEmbedding.Paper.IncrementsCoordinateMetricVariation
import GlobalEmbedding.Paper.IncrementsCoordinateGramGeometry

/-!
# Actual Gram-reconstructed first variation on the original open chart

Source: `main.tex`, lem:increments617–620. W2.
Only smoothness and immersion on the original open coordinate domain are used.
The actual Z is reconstructed from the actual F/u/normal field. No desired
first variation, pairing or cancellation identity is an input.
-/

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- The actual induced metric variation for Z=dF(g^-1u)+v on the SAME original
open chart. The accepted actual Gram right inverse is smooth there and yields
Z's true differentiability. Accepted actual lowering gives the covector pairing
on the open domain; native germ differentiation recovers the original u. Apply
the accepted literal metric variation and actual Hessian Gamma/B decomposition.
No global Euclidean smooth extension is assumed. Source: lem:increments617–620. -/
theorem increments_gram_linearized_metric {n N : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (hF : ContDiffOn ℝ ∞ F Ω)
    (hinj : ∀ y ∈ Ω, Function.Injective (fderiv ℝ F y))
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (ν : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (hnormal : ∀ y ∈ Ω, ν y ∈ (LinearMap.range (fderiv ℝ F y).toLinearMap)ᗮ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (hu : DifferentiableAt ℝ u x) (hν : DifferentiableAt ℝ ν x)
    (v w : EuclideanSpace ℝ (Fin n)) :
    let A := fderiv ℝ F x
    let H := fderiv ℝ (fderiv ℝ F) x v w
    let Z := fun y ↦ freeGramRightInverse (fderiv ℝ F y) (u y) + ν y
    HasDerivAt (fun s : ℝ ↦ inducedMetric (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun y ↦ F y + s • Z y) x
      ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm v)
      ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm w))
      (inner ℝ (fderiv ℝ u x v) w + inner ℝ (fderiv ℝ u x w) v -
        2 * inner ℝ ((A.adjoint.comp A).inverse (A.adjoint H)) (u x) -
        2 * inner ℝ ((LinearMap.range A.toLinearMap)ᗮ.starProjection H) (ν x)) 0 := by
  let A := fun y ↦ fderiv ℝ F y
  let Z := fun y ↦ freeGramRightInverse (A y) (u y) + ν y
  have hFx : ContDiffAt ℝ ∞ F x := (hF x hx).contDiffAt (hΩ.mem_nhds hx)
  have hAs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin N)) ∞ A Ω := by
    intro y hy
    exact (((hF y hy).contDiffAt (hΩ.mem_nhds hy)).fderiv_right
      (m := ∞) (by simp)).contMDiffAt.contMDiffWithinAt
  have hJ := freeGramRightInverse_contMDiffOn A hAs hinj
  have hJx := ((hJ.contDiffOn x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hZ : DifferentiableAt ℝ Z x := (hJx.clm_apply hu).add hν
  have hlower (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ Ω) :
      (A y).adjoint (Z y) = u y := by
    have hh := increments_gram_reconstruction_lowering F y (u y) (ν y)
      (hinj y hy) (hnormal y hy)
    simpa only [A, Z, freeGramRightInverse, ContinuousLinearMap.comp_apply] using hh
  have hpair (d : EuclideanSpace ℝ (Fin n)) :
      (fun y ↦ inner ℝ (fderiv ℝ F y d) (Z y)) =ᶠ[𝓝 x]
        fun y ↦ inner ℝ (u y) d := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    have hh := ContinuousLinearMap.adjoint_inner_left (A y) d (Z y)
    rw [hlower y hy] at hh
    exact ((real_inner_comm (Z y) (A y d)).trans hh.symm)
  have hdPair (d t : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y ↦ inner ℝ (fderiv ℝ F y d) (Z y)) x t =
        inner ℝ (fderiv ℝ u x t) d := by
    rw [(hpair d).fderiv_eq, fderiv_inner_apply ℝ hu (differentiableAt_const d)]
    simp
  have hmetric := increments_metric_variation_lowered_pairings F Z x v w
    (hFx.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)) hZ
  rw [hdPair w v, hdPair v w] at hmetric
  have hsplit := increments_hessian_pairing_gram_normal F x v w (u x) (ν x)
    (hinj x hx) (hnormal x hx)
  change inner ℝ (fderiv ℝ (fderiv ℝ F) x v w) (Z x) =
    inner ℝ (((A x).adjoint.comp (A x)).inverse
      ((A x).adjoint (fderiv ℝ (fderiv ℝ F) x v w))) (u x) +
    inner ℝ ((LinearMap.range (A x).toLinearMap)ᗮ.starProjection
      (fderiv ℝ (fderiv ℝ F) x v w)) (ν x) at hsplit
  have hd := increments_inducedMetric_hasDerivAt F Z x v w
    (hFx.differentiableAt (by simp)) hZ
  exact hd.congr_deriv (by have ht := hd.deriv; linarith)

end GlobalEmbedding.Paper
