import GlobalEmbedding.Paper.BalancedFixedTranslatedSourceData

/-!
# Construct actual little Hölder source data on arbitrary finite-dimensional parameters

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
lines 403–418. DAG node: `balanced-source-little-data-existence`.
-/

open Set WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Original smooth periodic pointwise sources construct actual little forcing and
bounded multiplication operators on any finite-dimensional real normed parameter space.
Their exact source values, original norm smoothness and actual jointly translated
forcing/conjugated multiplier smoothness hold on the original open domain only.

Proof: choose genuine finite-dimensional continuous linear coordinates and pull the open
domain and both sources back along the inverse coordinates. Apply the already proved
Euclidean source-to-little-data construction. Pull its actual forcing and multiplication
operators back to the original parameters; the inverse laws give their exact source values.
The already proved general-parameter source-value theorem then gives original norm C∞
and jointly translated/conjugated C∞, without assuming any carrier or norm regularity.
Empty domains and zero parameter, fiber, input and output dimensions are included.
Source: actual local source-data construction in `lem:balanced`, lines 403–418. -/
theorem balanced_source_little_data_exists
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {a M N : ℕ} {α : ℝ} (U : Set P) (hU : IsOpen U)
    (sourceA : P → EuclideanSpace ℝ (Fin a) →
      (EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin N)))
    (sourcef : P → EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hsA : ContDiffOn ℝ ∞ (Function.uncurry sourceA) (U ×ˢ univ))
    (hsf : ContDiffOn ℝ ∞ (Function.uncurry sourcef) (U ×ˢ univ))
    (hperiodA : ∀ p ∈ U, ∀ (x : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ),
      sourceA p (x + toLp 2 (fun i ↦ (m i : ℝ))) = sourceA p x)
    (hperiodf : ∀ p ∈ U, ∀ (x : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ),
      sourcef p (x + toLp 2 (fun i ↦ (m i : ℝ))) = sourcef p x)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ f : P → LittlePeriodicCAlphaFunction a N 2 α,
      ∃ A : P → LittlePeriodicCAlphaFunction a M 2 α →L[ℝ]
          LittlePeriodicCAlphaFunction a N 2 α,
        (∀ p ∈ U, ∀ x, (f p).val.toFun x = sourcef p x) ∧
        (∀ p ∈ U, ∀ (u : LittlePeriodicCAlphaFunction a M 2 α) x,
          (A p u).val.toFun x = sourceA p x (u.val.toFun x)) ∧
        ContDiffOn ℝ ∞ f U ∧ ContDiffOn ℝ ∞ A U ∧
        ContDiffOn ℝ ∞ (fun z : P × EuclideanSpace ℝ (Fin a) ↦
          littlePeriodicCAlphaTranslateIsometry z.2 (f z.1)) (U ×ˢ univ) ∧
        ContDiffOn ℝ ∞ (fun z : P × EuclideanSpace ℝ (Fin a) ↦
          (littlePeriodicCAlphaTranslateIsometry z.2).toContinuousLinearMap.comp
            ((A z.1).comp
              (littlePeriodicCAlphaTranslateIsometry (-z.2)).toContinuousLinearMap))
          (U ×ˢ univ) := by
  let e : P ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ P)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let W := e.symm ⁻¹' U
  have hW : IsOpen W := hU.preimage e.symm.continuous
  let ca := fun p x ↦ sourceA (e.symm p) x
  let cf := fun p x ↦ sourcef (e.symm p) x
  have hin : ContDiff ℝ ∞ (fun z :
      EuclideanSpace ℝ (Fin (Module.finrank ℝ P)) × EuclideanSpace ℝ (Fin a) ↦
        (e.symm z.1, z.2)) :=
    (e.symm.contDiff.comp contDiff_fst).prodMk contDiff_snd
  have hca : ContDiffOn ℝ ∞ (Function.uncurry ca) (W ×ˢ univ) :=
    hsA.comp hin.contDiffOn (fun z hz ↦ ⟨hz.1, hz.2⟩)
  have hcf : ContDiffOn ℝ ∞ (Function.uncurry cf) (W ×ˢ univ) :=
    hsf.comp hin.contDiffOn (fun z hz ↦ ⟨hz.1, hz.2⟩)
  obtain ⟨fe, Ae, hfe, hAe, _, _⟩ := balanced_fixed_translated_data W hW ca cf hca hcf
    (fun p hp x m ↦ hperiodA (e.symm p) hp x m)
    (fun p hp x m ↦ hperiodf (e.symm p) hp x m) hα0 hα1
  let f := fun p ↦ fe (e p)
  let A := fun p ↦ Ae (e p)
  have hfvalue : ∀ p ∈ U, ∀ x, (f p).val.toFun x = sourcef p x := by
    intro p hp x
    have hw : e p ∈ W := by simpa only [W, mem_preimage, e.symm_apply_apply] using hp
    simpa only [cf, e.symm_apply_apply] using hfe (e p) hw x
  have hAvalue : ∀ p ∈ U, ∀ (u : LittlePeriodicCAlphaFunction a M 2 α) x,
      (A p u).val.toFun x = sourceA p x (u.val.toFun x) := by
    intro p hp u x
    have hw : e p ∈ W := by simpa only [W, mem_preimage, e.symm_apply_apply] using hp
    simpa only [ca, e.symm_apply_apply] using hAe (e p) hw u x
  exact ⟨f, A, hfvalue, hAvalue, balanced_fixed_translated_source_data U hU A f
    sourceA sourcef hsA hsf hperiodA hperiodf hAvalue hfvalue hα0 hα1⟩

#print axioms balanced_source_little_data_exists

end GlobalEmbedding.Paper
