import GlobalEmbedding.Paper.PeriodicCAlphaRestrictOrderNorm
import GlobalEmbedding.Paper.PeriodicCAlphaPointwiseOperations
import GlobalEmbedding.Paper.PeriodicCAlphaCarrierInjective

/-!
# Bounded actual ambient Hölder regularity inclusion

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-ambient-restrict-order`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- Lowering declared Hölder order is a genuine continuous linear map with unchanged lift.

The constructed lower carrier supplies the data. Actual pointwise operations prove its
linearity. Compactness supplies a finite actual flat-torus diameter; the proved full lower
norm bound gives continuity of the actual map. Source: regularity inclusions for vertical
translation derivatives in the proof of `lem:balanced`. -/
noncomputable def periodicCAlphaRestrictOrderContinuous {a N k : ℕ} {α : ℝ}
    (j : ℕ) (hj : j ≤ k) (hα : α ≤ 1) :
    PeriodicCAlphaFunction a N k α →L[ℝ] PeriodicCAlphaFunction a N j α := by
  let T : PeriodicCAlphaFunction a N k α →ₗ[ℝ] PeriodicCAlphaFunction a N j α :=
    { toFun := periodicCAlphaRestrictOrder j hj hα
      map_add' := by
        intro f g
        apply periodicCAlpha_toFun_injective
        funext x
        change (f + g).toFun x =
          (periodicCAlphaRestrictOrder j hj hα f + periodicCAlphaRestrictOrder j hj hα g).toFun x
        rw [(periodicCAlpha_pointwise_operations a N k α).2.1,
          (periodicCAlpha_pointwise_operations a N j α).2.1]
        rfl
      map_smul' := by
        intro c f
        apply periodicCAlpha_toFun_injective
        funext x
        change (c • f).toFun x = (c • periodicCAlphaRestrictOrder j hj hα f).toFun x
        rw [(periodicCAlpha_pointwise_operations a N k α).2.2,
          (periodicCAlpha_pointwise_operations a N j α).2.2]
        rfl }
  apply T.mkContinuousOfExistsBound
  have hcompact : IsCompact (univ : Set (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))) := by
    have hrange : Set.range (toLp 2 : (Fin a → AddCircle (1 : ℝ)) →
        PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) = univ :=
      Set.range_eq_univ.mpr (WithLp.equiv 2 (Fin a → AddCircle (1 : ℝ))).symm.surjective
    rw [← hrange]
    exact isCompact_range (PiLp.continuous_toLp _ _)
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp hcompact.isBounded
  exact ⟨_, fun f ↦ periodicCAlphaRestrictOrder_norm j hj hα f D
    (fun x y ↦ hD (mem_univ _) (mem_univ _))⟩

#print axioms periodicCAlphaRestrictOrderContinuous

end GlobalEmbedding.Paper
