import GlobalEmbedding.Paper.TruePhaseMarginSpecification
import GlobalEmbedding.Paper.PointwiseJetNormalBound
import GlobalEmbedding.Paper.PhaseStabilityTransportUniform
import GlobalEmbedding.Paper.TrueSecondFormProjectedJet

open Bundle Manifold
open scoped TensorProduct ContDiff

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance phaseSquareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance phaseSquareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- Uniform two-jet stability of the actual true phase margin.

The positive tolerance depends only on the reference ellipticity, second-jet
bound, selector lower bound and inverse hyperplane-transport bound. All first
and symmetric second jets use the actual fixed auxiliary tangent metric. The
reference jets may be the source ideal jets; the perturbed jets are identified
with an actual smooth map. The conclusion includes quarter-Gram ellipticity,
the quantitative entire projected-jet error and a positive lower bound for the
actual normal-valued phase margin and an actual good unit covector.

Proof: choose C=1+L², k=(3/√λ)max(0,M), D=1+k and
δ=min(√λ/2,m/(4CD)). Apply the existing pointwise projected-jet theorem. The
canonical symmetric-square kernel inclusion is isometric, hence restriction
does not increase the difference norm. The actual transported selector bound
then retains m/(2C). The entire true-form jet identity and the induced normal
norm identify this lower bound with the actual phase margin and injectivity.
Source: `prop:initialization`, selector-margin stability, and `defn:phase`. -/
theorem initialization_phase_stability
    {E H M V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [RiemannianBundle (TangentSpace I : M → Type _)]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {N : ℕ}
    (hdim : 2 ≤ Module.finrank ℝ E) (lam bound m L : ℝ)
    (hlam : 0 < lam) (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ (g : M → EuclideanSpace ℝ (Fin N))
      (hg : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ g)
      (A B : ∀ x : M, TangentSpace I x →L[ℝ] EuclideanSpace ℝ (Fin N))
      (Q Q' : ∀ x : M, SymmetricSquare (TangentSpace I x) →L[ℝ] EuclideanSpace ℝ (Fin N))
      (ξ : ∀ x : M, TangentSpace I x →L[ℝ] ℝ)
      (e : ∀ x : M, (ξ x).ker ≃L[ℝ] V)
      (S : M → SymmetricSquare V →L[ℝ] EuclideanSpace ℝ (Fin N)),
      (∀ x v, lam * ‖v‖ ^ 2 ≤ ‖A x v‖ ^ 2) →
      (∀ x, ‖Q x‖ ≤ bound) →
      (∀ x, ‖A x - B x‖ ≤ δ) → (∀ x, ‖Q' x - Q x‖ ≤ δ) →
      (∀ x, ‖ξ x‖ = 1) → (∀ x, ‖(e x).symm.toContinuousLinearMap‖ ≤ L) →
      (∀ x, covectorRestriction (E := TangentSpace I x) (F := EuclideanSpace ℝ (Fin N)) ((LinearMap.range (A x).toLinearMap)ᗮ.starProjection.comp (Q x))
        (ξ x) = (S x).comp (symmetricSquareMapL (e x).toContinuousLinearMap)) →
      (∀ x z, m * ‖z‖ ≤ ‖S x z‖) →
      (∀ x, B x =
        (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (g x)).toContinuousLinearMap.comp
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) g x)) →
      (∀ x (v w : TangentSpace I x),
        Q' x (symmetricSquareProduct (TangentSpace I x) v w) =
          fderiv ℝ (fderiv ℝ (g ∘ (extChartAt I x).symm)) (extChartAt I x x)
            (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w)) →
      ∀ x,
        (∀ v, (lam / 4) * ‖v‖ ^ 2 ≤ ‖B x v‖ ^ 2) ∧
        (‖(LinearMap.range (B x).toLinearMap)ᗮ.starProjection -
          (LinearMap.range (A x).toLinearMap)ᗮ.starProjection‖ ≤
          (3 / Real.sqrt lam) * ‖A x - B x‖) ∧
        (‖(LinearMap.range (B x).toLinearMap)ᗮ.starProjection.comp (Q' x) -
          (LinearMap.range (A x).toLinearMap)ᗮ.starProjection.comp (Q x)‖ ≤
          ‖Q' x - Q x‖ + (3 / Real.sqrt lam) * bound * ‖A x - B x‖) ∧
        m / (2 * (1 + L ^ 2)) ≤ truePhaseMargin g hg x ∧
        Function.Injective (covectorRestriction (E := TangentSpace I x) (F := normalSpace (I := I) g x) (trueSecondFormL g hg x) (ξ x)) := by
  let C : ℝ := 1 + L ^ 2
  let k : ℝ := (3 / Real.sqrt lam) * max 0 bound
  let D : ℝ := 1 + k
  have hC : 0 < C := by dsimp [C]; positivity
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  let δ := min (Real.sqrt lam / 2) (m / (4 * C * D))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδfirst : δ ≤ Real.sqrt lam / 2 := min_le_left _ _
  have hproduct : D * δ ≤ m / (4 * C) := by
    have hd := (le_div_iff₀ (by positivity : 0 < 4 * C * D)).mp (min_le_right
      (Real.sqrt lam / 2) (m / (4 * C * D)))
    apply (le_div_iff₀ (by positivity : 0 < 4 * C)).mpr
    nlinarith [hd]
  have hsmall : D * δ < m / (2 * C) := by
    apply lt_of_le_of_lt hproduct
    apply (div_lt_div_iff₀ (by positivity : 0 < 4 * C) (by positivity : 0 < 2 * C)).mpr
    nlinarith
  refine ⟨δ, hδ, ?_⟩
  intro g hg A B Q Q' ξ e S hA hQ hAB hDQ hξ hinv hselector hS hB hQg x
  let R : SymmetricSquare (TangentSpace I x) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    (LinearMap.range (A x).toLinearMap)ᗮ.starProjection.comp (Q x)
  let R' : SymmetricSquare (TangentSpace I x) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    (LinearMap.range (B x).toLinearMap)ᗮ.starProjection.comp (Q' x)
  have hp := pointwise_projected_jet_estimate (A x) (B x) (Q x) (Q' x) lam bound
    hlam (hA x) ((hAB x).trans hδfirst) (hQ x)
  have hgap := (pointwise_projected_jet_estimate (A x) (B x)
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N)))
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N))) lam 1
    hlam (hA x) ((hAB x).trans hδfirst) ContinuousLinearMap.norm_id_le).2
  have hprojection : ‖(LinearMap.range (B x).toLinearMap)ᗮ.starProjection -
      (LinearMap.range (A x).toLinearMap)ᗮ.starProjection‖ ≤
      (3 / Real.sqrt lam) * ‖A x - B x‖ := by simpa using hgap
  have hcoef : (3 / Real.sqrt lam) * bound ≤ k :=
    mul_le_mul_of_nonneg_left (le_max_right 0 bound) (by positivity)
  have herror : ‖R' - R‖ ≤ D * δ := by
    apply hp.2.trans
    calc
      ‖Q' x - Q x‖ + (3 / Real.sqrt lam) * bound * ‖A x - B x‖ ≤
          δ + k * δ := add_le_add (hDQ x)
            ((mul_le_mul_of_nonneg_right hcoef (norm_nonneg (A x - B x))).trans
              (mul_le_mul_of_nonneg_left (hAB x) hk))
      _ = D * δ := by dsimp [D]; ring
  have hrestrict : ‖covectorRestriction (E := TangentSpace I x) (F := EuclideanSpace ℝ (Fin N)) R' (ξ x) - covectorRestriction (E := TangentSpace I x) (F := EuclideanSpace ℝ (Fin N)) R (ξ x)‖ ≤
      ‖R' - R‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    have he := (R' - R).le_opNorm (symmetricSquareMapL (ξ x).ker.subtypeL z)
    rw [symmetric_square_subspace_isometry (ξ x).ker z] at he
    exact he
  have herr : ‖covectorRestriction (E := TangentSpace I x) (F := EuclideanSpace ℝ (Fin N)) R' (ξ x) -
      (S x).comp (symmetricSquareMapL (e x).toContinuousLinearMap)‖ < m / (2 * C) := by
    rw [← hselector x]
    exact (hrestrict.trans herror).trans_lt hsmall
  have htrans := (phase_stability_transport_uniform_lower_bound (e x) (S x)
    (covectorRestriction (E := TangentSpace I x) (F := EuclideanSpace ℝ (Fin N)) R' (ξ x)) m L hm (hinv x) (hS x) herr).2
  have ht : 2 ≤ Module.finrank ℝ (TangentSpace I x) := by
    rwa [(tangentSpaceCastModel I x).toLinearEquiv.finrank_eq]
  have hTf := trueSecondForm_eq_projected_coordinate_jet g hg x (Q' x).toLinearMap (hQg x)
  have hn : normalSpace (I := I) g x = (LinearMap.range (B x).toLinearMap)ᗮ := by
    rw [hB x]
    rfl
  have hpf : (normalSpace (I := I) g x).starProjection =
      (LinearMap.range (B x).toLinearMap)ᗮ.starProjection := by rw [hn]
  rw [hpf] at hTf
  have heq : R'.toLinearMap = (normalSpace (I := I) g x).subtype.comp
      (trueSecondForm g hg x) := hTf.symm
  have hmargin := (true_phase_margin_specification hdim g hg x).2.2.2 R' heq
  have hbest := (best_phase_supremum_specification ht R').2.2.2
    (ξ x) (m / (2 * C)) (hξ x) htrans
  have hmap : R' = (normalSpace (I := I) g x).subtypeL.comp (trueSecondFormL g hg x) := by
    apply ContinuousLinearMap.ext
    intro z
    exact congrArg (fun t : SymmetricSquare (TangentSpace I x) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin N) ↦ t z) heq
  have hlower : ∀ z, (m / (2 * C)) * ‖z‖ ≤
      ‖covectorRestriction (E := TangentSpace I x) (F := normalSpace (I := I) g x) (trueSecondFormL g hg x) (ξ x) z‖ := by
    intro z
    have he := htrans z
    rw [hmap] at he
    exact he
  have : Nontrivial (ξ x).ker := covector_kernel_nontrivial ht (ξ x)
  have : Nontrivial (SymmetricSquare (ξ x).ker) := symmetric_square_nontrivial
  have hleast := (least_singular_norm_bound (E := SymmetricSquare (ξ x).ker)
    (F := normalSpace (I := I) g x)
    (covectorRestriction (E := TangentSpace I x) (F := normalSpace (I := I) g x) (trueSecondFormL g hg x) (ξ x))).2.2 (m / (2 * C)) |>.mpr hlower
  have hgood := (covector_restriction_bound ht (trueSecondFormL g hg x) (ξ x)).2.2.mp
    ((div_pos hm (by positivity : 0 < 2 * C)).trans_le hleast)
  exact ⟨hp.1, hprojection, hp.2, hbest.trans_eq hmargin, hgood⟩

end GlobalEmbedding.Paper
