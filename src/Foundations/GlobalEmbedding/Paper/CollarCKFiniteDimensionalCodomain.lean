import GlobalEmbedding.Paper.CollarCKAnalyticRealization
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# First-order CK with a finite-dimensional real output

Source: Gantumur, notes2, Theorem18 and Corollary20. Transport only the output coordinates
through the native continuous linear equivalence of a finite basis. Invoke the accepted
original-data theorem once, on the same spatial domain and the same product ball, and restore
both the constructed solution and every competing analytic function. Zero dimensions are allowed.
-/

noncomputable section
open scoped Topology
namespace GlobalEmbedding.Paper

/-- The full original first-order CK conclusion for any finite-dimensional real output space.
Source: Gantumur, Theorem18 and Corollary20, invariance under finite linear output coordinates.
Use the native finite basis coordinate equivalence, conjugate values and every spatial jet slot,
and call the accepted original-data theorem once. Native linear chain rules identify the actual
PDE and initial data before and after this conjugation. Every analytic competitor is conjugated
by the same equivalence, so the positive uniqueness radius and both radius bounds are unchanged.
No positivity of the spatial dimension or output dimension, norm isometry, supplied coordinate
dictionary, formal compatibility, convergence bound or desired analytic solution is assumed. -/
theorem collarCKFiniteDimensionalExistenceUnique
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (G : EuclideanSpace ℝ (Fin n) × ℝ × F × (Fin n → F) → F)
    (v₀ : EuclideanSpace ℝ (Fin n) → F) (x₀ : EuclideanSpace ℝ (Fin n))
    (hv₀ : AnalyticAt ℝ v₀ x₀)
    (hG : AnalyticAt ℝ G
      (x₀, 0, v₀ x₀, fun i ↦ fderiv ℝ v₀ x₀ (EuclideanSpace.single i (1 : ℝ)))) :
    ∃ ε > 0, ∃ u : ℝ × EuclideanSpace ℝ (Fin n) → F,
      AnalyticOnNhd ℝ u (Metric.ball (0, x₀) ε) ∧
      (∀ r x, (r, x) ∈ Metric.ball (0, x₀) ε →
        fderiv ℝ u (r, x) (1, 0) =
          G (x, r, u (r, x), fun i ↦ fderiv ℝ u (r, x) (0, EuclideanSpace.single i 1))) ∧
      (∀ x, x ∈ Metric.ball x₀ ε → u (0, x) = v₀ x) ∧
      (∀ v η, 0 < η → AnalyticOnNhd ℝ v (Metric.ball (0, x₀) η) →
        (∀ r x, (r, x) ∈ Metric.ball (0, x₀) η →
          fderiv ℝ v (r, x) (1, 0) =
            G (x, r, v (r, x), fun i ↦ fderiv ℝ v (r, x) (0, EuclideanSpace.single i 1))) →
        (∀ x, x ∈ Metric.ball x₀ η → v (0, x) = v₀ x) →
        ∃ δ > 0, δ ≤ ε ∧ δ ≤ η ∧
          ∀ r x, (r, x) ∈ Metric.ball (0, x₀) δ → u (r, x) = v (r, x)) := by
  let k := Module.finrank ℝ F
  let e : F ≃L[ℝ] (Fin k → ℝ) := (Module.finBasis ℝ F).equivFunL
  let a : EuclideanSpace ℝ (Fin n) → Fin k → ℝ := e ∘ v₀
  let T : (EuclideanSpace ℝ (Fin n) × ℝ × (Fin k → ℝ) × (Fin n → Fin k → ℝ)) →
      EuclideanSpace ℝ (Fin n) × ℝ × F × (Fin n → F) :=
    fun z ↦ (z.1, z.2.1, e.symm z.2.2.1, fun i ↦ e.symm (z.2.2.2 i))
  let G' := e ∘ G ∘ T
  have ha : AnalyticAt ℝ a x₀ := (e.toContinuousLinearMap.analyticAt _).comp hv₀
  have hader : fderiv ℝ a x₀ = e.toContinuousLinearMap.comp (fderiv ℝ v₀ x₀) :=
    (e.hasFDerivAt.comp x₀ hv₀.differentiableAt.hasFDerivAt).fderiv
  have hT : AnalyticAt ℝ T
      (x₀, 0, a x₀, fun i ↦ fderiv ℝ a x₀ (EuclideanSpace.single i 1)) := by
    have hx := analyticAt_fst (𝕜 := ℝ)
      (p := (x₀, (0 : ℝ), a x₀, fun i ↦ fderiv ℝ a x₀ (EuclideanSpace.single i 1)))
    have ht := analyticAt_fst.comp (analyticAt_snd (𝕜 := ℝ)
      (p := (x₀, (0 : ℝ), a x₀, fun i ↦ fderiv ℝ a x₀ (EuclideanSpace.single i 1))))
    have hy : AnalyticAt ℝ
        (fun z : EuclideanSpace ℝ (Fin n) × ℝ × (Fin k → ℝ) × (Fin n → Fin k → ℝ) ↦
          e.symm z.2.2.1)
        (x₀, 0, a x₀, fun i ↦ fderiv ℝ a x₀ (EuclideanSpace.single i 1)) :=
      (e.symm.toContinuousLinearMap.analyticAt _).comp
        (analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd))
    have hq : AnalyticAt ℝ
        (fun z : EuclideanSpace ℝ (Fin n) × ℝ × (Fin k → ℝ) × (Fin n → Fin k → ℝ) ↦
          fun i ↦ e.symm (z.2.2.2 i))
        (x₀, 0, a x₀, fun i ↦ fderiv ℝ a x₀ (EuclideanSpace.single i 1)) := by
      apply AnalyticAt.pi
      intro i
      exact (e.symm.toContinuousLinearMap.analyticAt _).comp
        (((ContinuousLinearMap.proj i :
          (Fin n → Fin k → ℝ) →L[ℝ] (Fin k → ℝ)).analyticAt _).comp
            (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)))
    exact hx.prod (ht.prod (hy.prod hq))
  have hT0 : T (x₀, 0, a x₀, fun i ↦ fderiv ℝ a x₀ (EuclideanSpace.single i 1)) =
      (x₀, 0, v₀ x₀, fun i ↦ fderiv ℝ v₀ x₀ (EuclideanSpace.single i 1)) := by
    simp only [T, a, Function.comp_apply, hader, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  have hG' : AnalyticAt ℝ G'
      (x₀, 0, a x₀, collarCKInitialSpatialJet a x₀) :=
    (e.toContinuousLinearMap.analyticAt _).comp (hG.comp_of_eq hT hT0)
  have hPDE (v : ℝ × EuclideanSpace ℝ (Fin n) → F)
      (z : ℝ × EuclideanSpace ℝ (Fin n)) (hv : DifferentiableAt ℝ v z) :
      (fderiv ℝ (e ∘ v) z (1, 0) = G'
        (z.2, z.1, (e ∘ v) z,
          fun i ↦ fderiv ℝ (e ∘ v) z (0, EuclideanSpace.single i 1))) ↔
      (fderiv ℝ v z (1, 0) =
        G (z.2, z.1, v z, fun i ↦ fderiv ℝ v z (0, EuclideanSpace.single i 1))) := by
    have hd : fderiv ℝ (e ∘ v) z = e.toContinuousLinearMap.comp (fderiv ℝ v z) :=
      (e.hasFDerivAt.comp z hv.hasFDerivAt).fderiv
    simp only [hd, G', T, Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply, e.injective.eq_iff]
  obtain ⟨ε, hε, w, hw, hwPDE, hwi, hwuniq⟩ :=
    collarCKOriginalExistenceUnique G' a x₀ ha hG'
  let u : ℝ × EuclideanSpace ℝ (Fin n) → F := e.symm ∘ w
  have hu : AnalyticOnNhd ℝ u (Metric.ball (0, x₀) ε) := by
    intro z hz
    exact (e.symm.toContinuousLinearMap.analyticAt _).comp (hw z hz)
  have heu : e ∘ u = w := by
    funext z
    simp [u]
  refine ⟨ε, hε, u, hu, ?_, ?_, ?_⟩
  · intro r x hx
    apply (hPDE u (r, x) (hu _ hx).differentiableAt).mp
    simpa only [heu] using hwPDE r x hx
  · intro x hx
    change e.symm (w (0, x)) = v₀ x
    rw [hwi x hx]
    exact e.symm_apply_apply (v₀ x)
  · intro v η hη hv hvPDE hvi
    have hev : AnalyticOnNhd ℝ (e ∘ v) (Metric.ball (0, x₀) η) := by
      intro z hz
      exact (e.toContinuousLinearMap.analyticAt _).comp (hv z hz)
    have hevPDE : ∀ r x, (r, x) ∈ Metric.ball (0, x₀) η →
        fderiv ℝ (e ∘ v) (r, x) (1, 0) = G'
          (x, r, (e ∘ v) (r, x),
            fun i ↦ fderiv ℝ (e ∘ v) (r, x) (0, EuclideanSpace.single i 1)) := by
      intro r x hx
      exact (hPDE v (r, x) (hv _ hx).differentiableAt).mpr (hvPDE r x hx)
    have hevi : ∀ x, x ∈ Metric.ball x₀ η → (e ∘ v) (0, x) = a x := by
      intro x hx
      exact congrArg e (hvi x hx)
    obtain ⟨δ, hδ, hδε, hδη, hEq⟩ := hwuniq (e ∘ v) η hη hev hevPDE hevi
    refine ⟨δ, hδ, hδε, hδη, ?_⟩
    intro r x hx
    apply e.injective
    change (e ∘ u) (r, x) = (e ∘ v) (r, x)
    rw [heu]
    exact hEq r x hx

#print axioms collarCKFiniteDimensionalExistenceUnique
end GlobalEmbedding.Paper
