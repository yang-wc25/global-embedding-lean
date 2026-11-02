import GlobalEmbedding.Paper.CollarHolderMixedBilinearExtension

/-!
# Actual pointwise complex multipliers from proved real product data

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. A matrix coefficient must act through an actual operator-norm analytic
multiplier family. The real product norm estimate remains a separate, explicit prerequisite.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- A genuinely bounded actual real little-Hölder product with its true pointwise formula
constructs the actual complex pointwise multiplier CLM and an operator-norm analytic family
for every actual analytic coefficient family.

Source: Proposition `prop:collar`, proof lines 530–534, analytic coefficient multipliers.
Complexify the actual real bounded product between the proved actual little spaces. Its real
inclusions are the actual pointwise ofReal maps. Any real form supplied by the closed-real-form
theorem has the same inclusion, by function injectivity. Thus every complex input decomposes
into these actual real inclusions. On two real inputs the extension's pointwise formula is
exactly the given finite-dimensional complex product. Expand both complex inputs into their
real and imaginary parts; genuine complex bilinearity and bounded complex evaluation force
the same pointwise formula on all complex inputs. The resulting coefficient-to-operator map
is an actual complex CLM. Composing it with the actual analytic coefficient family gives
AnalyticAt in the actual operator norm. No real product bound is silently assumed proved.
-/
theorem collar_holder_pointwise_multiplier
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {a M N P k : ℕ} {α : ℝ}
    (Q : LittlePeriodicCAlphaFunction a M k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α →L[ℝ] LittlePeriodicCAlphaFunction a P k α)
    (B : EuclideanSpace ℂ (Fin M) →L[ℂ]
      EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin P))
    (hQ : ∀ u v (y : EuclideanSpace ℝ (Fin a)),
      toLp 2 (fun i : Fin P ↦ ((Q u v : PeriodicCAlphaFunction a P k α).toFun y i : ℂ)) =
        B (toLp 2 (fun i : Fin M ↦ ((u : PeriodicCAlphaFunction a M k α).toFun y i : ℂ)))
          (toLp 2 (fun i : Fin N ↦ ((v : PeriodicCAlphaFunction a N k α).toFun y i : ℂ))))
    (A : Z → CollarComplexHolderSpace a M k α) (z₀ : Z) (hA : AnalyticAt ℂ A z₀) :
    ∃ C : CollarComplexHolderSpace a M k α →L[ℂ]
        CollarComplexHolderSpace a N k α →L[ℂ] CollarComplexHolderSpace a P k α,
      (∀ f u (y : EuclideanSpace ℝ (Fin a)),
        collarComplexHolderFunction (C f u) y =
          B (collarComplexHolderFunction f y) (collarComplexHolderFunction u y)) ∧
      AnalyticAt ℂ (fun z ↦ C (A z)) z₀ := by
  obtain ⟨jM, jN, jP, hjM, hjN, hjP, C, hreal, _⟩ :=
    collar_holder_mixed_bilinear_extension Q
  obtain ⟨iM, rM, sM, hiM, _, _, hdM, _, _, _⟩ :=
    collar_complex_holder_real_form (a := a) (N := M) (k := k) (α := α)
  obtain ⟨iN, rN, sN, hiN, _, _, hdN, _, _, _⟩ :=
    collar_complex_holder_real_form (a := a) (N := N) (k := k) (α := α)
  have heqM : iM = jM := by
    apply ContinuousLinearMap.ext
    intro u
    apply collarComplexHolderFunction_injective
    funext y
    rw [hiM, hjM]
  have heqN : iN = jN := by
    apply ContinuousLinearMap.ext
    intro u
    apply collarComplexHolderFunction_injective
    funext y
    rw [hiN, hjN]
  have hdM' (f : CollarComplexHolderSpace a M k α) :
      jM (rM f) + Complex.I • jM (sM f) = f := by simpa only [heqM] using hdM f
  have hdN' (f : CollarComplexHolderSpace a N k α) :
      jN (rN f) + Complex.I • jN (sN f) = f := by simpa only [heqN] using hdN f
  have hpoint (u : LittlePeriodicCAlphaFunction a M k α)
      (v : LittlePeriodicCAlphaFunction a N k α) (y : EuclideanSpace ℝ (Fin a)) :
      collarComplexHolderFunction (C (jM u) (jN v)) y =
        B (collarComplexHolderFunction (jM u) y) (collarComplexHolderFunction (jN v) y) := by
    rw [hreal, hjP, hjM, hjN]
    exact hQ u v y
  refine ⟨C, ?_, (C.analyticAt (A z₀)).comp hA⟩
  intro f u y
  conv_lhs => rw [← hdM' f, ← hdN' u]
  conv_rhs => rw [← hdM' f, ← hdN' u]
  simp only [map_add, map_smul, add_apply, smul_apply,
    collarComplexHolderFunction_add, collarComplexHolderFunction_smul,
    Pi.add_apply, Pi.smul_apply, hpoint, smul_add, smul_smul]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_holder_pointwise_multiplier
