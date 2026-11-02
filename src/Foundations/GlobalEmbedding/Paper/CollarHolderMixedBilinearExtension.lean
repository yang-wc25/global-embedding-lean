import GlobalEmbedding.Paper.CollarComplexMixedBilinearExtension
import GlobalEmbedding.Paper.CollarComplexHolderRealForm
import GlobalEmbedding.Paper.CollarRealFormCoordinates

/-!
# Mixed bounded operators on the actual complex little Hölder spaces

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Matrix coefficients and vector functions have different target dimensions.
The actual bounded real product data must be complexified between their actual little spaces.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- Actual bounded real little-Hölder bilinear data on possibly different target spaces have an
actual unique bounded complex bilinear extension between their proved complex little spaces.

Source: Proposition `prop:collar`, proof lines 530–534, coefficient-to-operator complexification.
Choose the proved actual closed real forms for each of the three little spaces, retaining their
actual pointwise inclusion equations. The unique real/imaginary decompositions supply the
coordinate identities under I. Compose the actual real product with the target inclusion to
obtain real bounded bilinear data with complex target. Apply the mixed-input complexification
construction to the two actual source real forms. Agreement and uniqueness then give the
claimed actual complex coefficient-to-operator CLM. The real product itself is genuine bounded
input data, not a conclusion silently assumed for the source matrix multiplication theorem.
-/
theorem collar_holder_mixed_bilinear_extension {a M N P k : ℕ} {α : ℝ}
    (Q : LittlePeriodicCAlphaFunction a M k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α →L[ℝ] LittlePeriodicCAlphaFunction a P k α) :
    ∃ (jM : LittlePeriodicCAlphaFunction a M k α →L[ℝ] CollarComplexHolderSpace a M k α)
      (jN : LittlePeriodicCAlphaFunction a N k α →L[ℝ] CollarComplexHolderSpace a N k α)
      (jP : LittlePeriodicCAlphaFunction a P k α →L[ℝ] CollarComplexHolderSpace a P k α),
      (∀ u x, collarComplexHolderFunction (jM u) x =
        toLp 2 (fun i : Fin M ↦ ((u : PeriodicCAlphaFunction a M k α).toFun x i : ℂ))) ∧
      (∀ u x, collarComplexHolderFunction (jN u) x =
        toLp 2 (fun i : Fin N ↦ ((u : PeriodicCAlphaFunction a N k α).toFun x i : ℂ))) ∧
      (∀ u x, collarComplexHolderFunction (jP u) x =
        toLp 2 (fun i : Fin P ↦ ((u : PeriodicCAlphaFunction a P k α).toFun x i : ℂ))) ∧
      ∃ C : CollarComplexHolderSpace a M k α →L[ℂ]
          CollarComplexHolderSpace a N k α →L[ℂ] CollarComplexHolderSpace a P k α,
        (∀ u v, C (jM u) (jN v) = jP (Q u v)) ∧
        (∀ B : CollarComplexHolderSpace a M k α →L[ℂ]
            CollarComplexHolderSpace a N k α →L[ℂ] CollarComplexHolderSpace a P k α,
          (∀ u v, B (jM u) (jN v) = jP (Q u v)) → B = C) := by
  obtain ⟨jM, rM, sM, hjM, _, _, hdM, huM, _, _⟩ :=
    collar_complex_holder_real_form (a := a) (N := M) (k := k) (α := α)
  obtain ⟨jN, rN, sN, hjN, _, _, hdN, huN, _, _⟩ :=
    collar_complex_holder_real_form (a := a) (N := N) (k := k) (α := α)
  obtain ⟨jP, _, _, hjP, _, _, _, _, _, _⟩ :=
    collar_complex_holder_real_form (a := a) (N := P) (k := k) (α := α)
  obtain ⟨hrIM, hsIM, hrjM, hsjM⟩ :=
    collar_real_form_coordinate_identities jM rM sM hdM huM
  obtain ⟨hrIN, hsIN, hrjN, hsjN⟩ :=
    collar_real_form_coordinate_identities jN rN sN hdN huN
  let B : LittlePeriodicCAlphaFunction a M k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α →L[ℝ] CollarComplexHolderSpace a P k α :=
    (ContinuousLinearMap.compL ℝ (LittlePeriodicCAlphaFunction a N k α)
      (LittlePeriodicCAlphaFunction a P k α) (CollarComplexHolderSpace a P k α) jP).comp Q
  obtain ⟨C, _, hreal, huniq⟩ := collar_complex_mixed_bilinear_extension
    jM rM sM hdM hrIM hsIM hrjM hsjM jN rN sN hdN hrIN hsIN hrjN hsjN B
  exact ⟨jM, jN, jP, hjM, hjN, hjP, C, hreal, huniq⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_holder_mixed_bilinear_extension
