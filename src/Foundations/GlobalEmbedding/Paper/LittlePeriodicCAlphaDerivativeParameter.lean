import GlobalEmbedding.Paper.LittlePeriodicCAlphaDirectionalDerivative

/-!
# Actual linear dependence of the little Hölder derivative on its direction

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 399–418.
DAG node: `balanced-holder-directional-derivative-parameter`.
-/

namespace GlobalEmbedding.Paper

/-- For a fixed actual high-order little Hölder element, its directional derivative depends
continuously and linearly on the Euclidean direction.

The underlying lift is exactly x↦Df(x)v. The genuine derivative tensor gives direction
linearity, and the actual full norm bound gives the linear map continuity bound ‖f‖.
This is derivative data for translation parameters, without assuming differentiability of
the orbit map. Source: vertical translation derivatives in the proof of `lem:balanced`. -/
noncomputable def littlePeriodicCAlphaDerivativeParameter {a N k : ℕ} {α : ℝ}
    (f : LittlePeriodicCAlphaFunction a N (k + 1) α) :
    EuclideanSpace ℝ (Fin a) →L[ℝ] LittlePeriodicCAlphaFunction a N k α := by
  let D : EuclideanSpace ℝ (Fin a) →ₗ[ℝ] LittlePeriodicCAlphaFunction a N k α :=
    { toFun := fun v ↦ littlePeriodicCAlphaDirectionalDerivative v f
      map_add' := by
        intro v w
        apply Subtype.ext
        apply periodicCAlpha_toFun_injective
        funext x
        change fderiv ℝ f.val.toFun x (v + w) =
          ((littlePeriodicCAlphaDirectionalDerivative v f).val +
            (littlePeriodicCAlphaDirectionalDerivative w f).val).toFun x
        rw [(periodicCAlpha_pointwise_operations a N k α).2.1]
        exact (fderiv ℝ f.val.toFun x).map_add v w
      map_smul' := by
        intro c v
        apply Subtype.ext
        apply periodicCAlpha_toFun_injective
        funext x
        change fderiv ℝ f.val.toFun x (c • v) =
          (c • (littlePeriodicCAlphaDirectionalDerivative v f).val).toFun x
        rw [(periodicCAlpha_pointwise_operations a N k α).2.2]
        exact (fderiv ℝ f.val.toFun x).map_smul c v }
  exact D.mkContinuous ‖f‖ (fun v ↦ by
    change ‖periodicCAlphaDirectionalDerivative v f.val‖ ≤ ‖f.val‖ * ‖v‖
    simpa only [mul_comm] using periodicCAlphaDirectionalDerivative_norm v f.val)

#print axioms littlePeriodicCAlphaDerivativeParameter

end GlobalEmbedding.Paper
