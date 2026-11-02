import GlobalEmbedding.Paper.PeriodicCAlphaBilinearNorm
import GlobalEmbedding.Paper.PeriodicCAlphaPointwiseOperations
import GlobalEmbedding.Paper.PeriodicCAlphaCarrierInjective
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The actual continuous bilinear product on the original ambient Hölder carriers

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 396–418.
DAG node: `balanced-holder-ambient-bilinear-product`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- Actual pointwise multiplication by a continuous bilinear value map is a continuous bilinear
map on the ORIGINAL ambient Hölder carriers, for α≤1.

Use the constructed actual product as data. Actual pointwise operations and value-map
bilinearity prove both direction linearities. Compactness supplies a finite actual torus
diameter, and the full original norm estimate supplies a genuine uniform bilinear bound.
The continuous bilinear-map constructor retains these exact product values.
Source: bounded Holder multiplication in `lem:balanced`. -/
noncomputable def periodicCAlphaBilinearContinuous {a M N L k : ℕ} {α : ℝ}
    (B : EuclideanSpace ℝ (Fin M) →L[ℝ]
      EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin L)) (hα : α ≤ 1) :
    PeriodicCAlphaFunction a M k α →L[ℝ]
      PeriodicCAlphaFunction a N k α →L[ℝ] PeriodicCAlphaFunction a L k α := by
  let T : PeriodicCAlphaFunction a M k α →ₗ[ℝ]
      PeriodicCAlphaFunction a N k α →ₗ[ℝ] PeriodicCAlphaFunction a L k α :=
    { toFun := fun f ↦
        { toFun := periodicCAlphaBilinear B hα f
          map_add' := by
            intro g₁ g₂
            apply periodicCAlpha_toFun_injective
            funext x
            change B (f.toFun x) ((g₁ + g₂).toFun x) =
              (periodicCAlphaBilinear B hα f g₁ + periodicCAlphaBilinear B hα f g₂).toFun x
            rw [(periodicCAlpha_pointwise_operations a N k α).2.1,
              (periodicCAlpha_pointwise_operations a L k α).2.1]
            exact (B (f.toFun x)).map_add _ _
          map_smul' := by
            intro c g
            apply periodicCAlpha_toFun_injective
            funext x
            change B (f.toFun x) ((c • g).toFun x) =
              (c • periodicCAlphaBilinear B hα f g).toFun x
            rw [(periodicCAlpha_pointwise_operations a N k α).2.2,
              (periodicCAlpha_pointwise_operations a L k α).2.2]
            exact (B (f.toFun x)).map_smul c _ }
      map_add' := by
        intro f₁ f₂
        apply LinearMap.ext
        intro g
        apply periodicCAlpha_toFun_injective
        funext x
        change B ((f₁ + f₂).toFun x) (g.toFun x) =
          (periodicCAlphaBilinear B hα f₁ g + periodicCAlphaBilinear B hα f₂ g).toFun x
        rw [(periodicCAlpha_pointwise_operations a M k α).2.1,
          (periodicCAlpha_pointwise_operations a L k α).2.1]
        exact congrArg (fun Q ↦ Q (g.toFun x)) (B.map_add (f₁.toFun x) (f₂.toFun x))
      map_smul' := by
        intro c f
        apply LinearMap.ext
        intro g
        apply periodicCAlpha_toFun_injective
        funext x
        change B ((c • f).toFun x) (g.toFun x) =
          (c • periodicCAlphaBilinear B hα f g).toFun x
        rw [(periodicCAlpha_pointwise_operations a M k α).2.2,
          (periodicCAlpha_pointwise_operations a L k α).2.2]
        exact congrArg (fun Q ↦ Q (g.toFun x)) (B.map_smul c (f.toFun x)) }
  have hbound : ∃ C : ℝ, ∀ f g, ‖T f g‖ ≤ C * ‖f‖ * ‖g‖ := by
    have hcompact : IsCompact (univ : Set (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))) := by
      have hrange : Set.range (toLp 2 : (Fin a → AddCircle (1 : ℝ)) →
          PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) = univ :=
        Set.range_eq_univ.mpr (WithLp.equiv 2 (Fin a → AddCircle (1 : ℝ))).symm.surjective
      rw [← hrange]
      exact isCompact_range (PiLp.continuous_toLp _ _)
    obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp hcompact.isBounded
    have hdiam (x y : EuclideanSpace ℝ (Fin a)) :
        dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ≤ D :=
      hD (mem_univ _) (mem_univ _)
    exact ⟨_, fun f g ↦ periodicCAlphaBilinear_norm B hα f g D hdiam⟩
  exact T.mkContinuousOfExistsBound₂ hbound

#print axioms periodicCAlphaBilinearContinuous

end GlobalEmbedding.Paper
