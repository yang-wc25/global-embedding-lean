import GlobalEmbedding.Paper.IncrementsGramLinearizedMetric
import GlobalEmbedding.Paper.IncrementsOscillatoryMetricConjugation

/-!
# The actual complex linearized metric of the original single mode

Source: `main.tex`, lem:increments617–620. W2.
The SAME open-coordinate F supplies its actual Gram inverse, Christoffel and normal
Hessian. Both actual displacement components are reconstructed from the original
lowered u and normal fields; the left side is the literal complex-conjugated
inducedMetric derivative. No desired derivative or cancellation is assumed.
-/

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- The original complex single-mode first variation on the SAME open chart.

Apply the accepted genuine real Gram variation to the real and imaginary
amplitudes. Accepted smoothness of the actual Gram right inverse proves both
displacements differentiable. Their actual lowered pairings equal the original
u by the accepted actual Gram cancellation. Consume literal actual metric phase
conjugation and substitute those true identities. The resulting formula is
partial_i u_j+partial_j u_i−2Gamma_ij.u−2<B_ij,v> plus the actual
(i/tau)(dpsi_i u_j+dpsi_j u_i). In adapted coordinates psi=x1 this is precisely
the original delta term. Only the original open chart is used, without a global
Euclidean smooth extension. Source: lem:increments617–620. -/
theorem increments_complex_linearized_metric {n N : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (hF : ContDiffOn ℝ ∞ F Ω)
    (hinj : ∀ y ∈ Ω, Function.Injective (fderiv ℝ F y))
    (uR uI : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (νR νI : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (hnR : ∀ y ∈ Ω, νR y ∈ (LinearMap.range (fderiv ℝ F y).toLinearMap)ᗮ)
    (hnI : ∀ y ∈ Ω, νI y ∈ (LinearMap.range (fderiv ℝ F y).toLinearMap)ᗮ)
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (huR : DifferentiableAt ℝ uR x) (huI : DifferentiableAt ℝ uI x)
    (hνR : DifferentiableAt ℝ νR x) (hνI : DifferentiableAt ℝ νI x)
    (hψ : DifferentiableAt ℝ ψ x) (v w : EuclideanSpace ℝ (Fin n)) :
    let A := fderiv ℝ F x
    let H := fderiv ℝ (fderiv ℝ F) x v w
    let Γ := (A.adjoint.comp A).inverse (A.adjoint H)
    let B := (LinearMap.range A.toLinearMap)ᗮ.starProjection H
    let P := fun y ↦ freeGramRightInverse (fderiv ℝ F y) (uR y) + νR y
    let Q := fun y ↦ freeGramRightInverse (fderiv ℝ F y) (uI y) + νI y
    let R := fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
      (Complex.exp (((ψ y / τ : ℝ) : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).re)
    let S := fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
      (Complex.exp (((ψ y / τ : ℝ) : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).im)
    Complex.exp (-((ψ x / τ : ℝ) : ℂ) * Complex.I) *
      ((incrementsCoordinateMetricVariation F R x v w : ℂ) +
        Complex.I * (incrementsCoordinateMetricVariation F S x v w : ℂ)) =
      (inner ℝ (fderiv ℝ uR x v) w + inner ℝ (fderiv ℝ uR x w) v -
        2 * inner ℝ Γ (uR x) - 2 * inner ℝ B (νR x) : ℂ) +
      Complex.I * (inner ℝ (fderiv ℝ uI x v) w + inner ℝ (fderiv ℝ uI x w) v -
        2 * inner ℝ Γ (uI x) - 2 * inner ℝ B (νI x) : ℂ) +
      Complex.I * ((fderiv ℝ ψ x v / τ : ℂ) *
          ((inner ℝ (uR x) w : ℂ) + Complex.I * (inner ℝ (uI x) w : ℂ)) +
        (fderiv ℝ ψ x w / τ : ℂ) *
          ((inner ℝ (uR x) v : ℂ) + Complex.I * (inner ℝ (uI x) v : ℂ))) := by
  let A := fun y ↦ fderiv ℝ F y
  let P := fun y ↦ freeGramRightInverse (A y) (uR y) + νR y
  let Q := fun y ↦ freeGramRightInverse (A y) (uI y) + νI y
  have hFx : ContDiffAt ℝ ∞ F x := (hF x hx).contDiffAt (hΩ.mem_nhds hx)
  have hAs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin N)) ∞ A Ω := by
    intro y hy
    exact (((hF y hy).contDiffAt (hΩ.mem_nhds hy)).fderiv_right
      (m := ∞) (by simp)).contMDiffAt.contMDiffWithinAt
  have hJ := freeGramRightInverse_contMDiffOn A hAs hinj
  have hJx := ((hJ.contDiffOn x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hP : DifferentiableAt ℝ P x := (hJx.clm_apply huR).add hνR
  have hQ : DifferentiableAt ℝ Q x := (hJx.clm_apply huI).add hνI
  have hp := (increments_gram_linearized_metric Ω hΩ F hF hinj uR νR hnR x hx
    huR hνR v w).deriv
  have hq := (increments_gram_linearized_metric Ω hΩ F hF hinj uI νI hnI x hx
    huI hνI v w).deriv
  change incrementsCoordinateMetricVariation F P x v w = _ at hp
  change incrementsCoordinateMetricVariation F Q x v w = _ at hq
  have hlP : (A x).adjoint (P x) = uR x := by
    have h := increments_gram_reconstruction_lowering F x (uR x) (νR x)
      (hinj x hx) (hnR x hx)
    simpa only [A, P, freeGramRightInverse, ContinuousLinearMap.comp_apply] using h
  have hlQ : (A x).adjoint (Q x) = uI x := by
    have h := increments_gram_reconstruction_lowering F x (uI x) (νI x)
      (hinj x hx) (hnI x hx)
    simpa only [A, Q, freeGramRightInverse, ContinuousLinearMap.comp_apply] using h
  have hpairP (d : EuclideanSpace ℝ (Fin n)) :
      inner ℝ (A x d) (P x) = inner ℝ (uR x) d := by
    have h := ContinuousLinearMap.adjoint_inner_left (A x) d (P x)
    rw [hlP] at h
    exact (real_inner_comm (P x) (A x d)).trans h.symm
  have hpairQ (d : EuclideanSpace ℝ (Fin n)) :
      inner ℝ (A x d) (Q x) = inner ℝ (uI x) d := by
    have h := ContinuousLinearMap.adjoint_inner_left (A x) d (Q x)
    rw [hlQ] at h
    exact (real_inner_comm (Q x) (A x d)).trans h.symm
  have h := increments_scaled_oscillatory_metric_conjugation F P Q ψ τ x v w
    (hFx.differentiableAt (by simp)) hP hQ hψ
  dsimp only at h ⊢
  rw [hp, hq, hpairP w, hpairQ w, hpairP v, hpairQ v] at h
  simpa only [P, Q, A, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_ofNat] using h

end GlobalEmbedding.Paper
