import GlobalEmbedding.Paper.BalancedFixedTranslatedData

/-!
# Actual norm-smooth translated data on any finite-dimensional parameter domain

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–425.
DAG node: `balanced-fixed-translated-source-data`.
-/

open Set WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Original smooth periodic source values give actual norm-smooth data and their translates.

Use genuine continuous linear coordinates in the finite-dimensional parameter space to
apply the actual Euclidean source-data theorem internally. Original lift fidelity identifies
its genuine forcing and multipliers with the supplied original data. Smooth coordinate
pullback proves actual joint norm-smooth translated forcing and operator-norm-smooth
conjugated multipliers. Restriction to shift zero gives original norm-smooth f and A.
No norm regularity, solution selection, Q or exterior source regularity is assumed.
Source: original local coefficient and vertical translation argument in `lem:balanced`. -/
theorem balanced_fixed_translated_source_data
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {a M N : ℕ} {α : ℝ} (U : Set P) (hU : IsOpen U)
    (A : P → LittlePeriodicCAlphaFunction a M 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α)
    (f : P → LittlePeriodicCAlphaFunction a N 2 α)
    (sourceA : P → EuclideanSpace ℝ (Fin a) →
      (EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin N)))
    (sourcef : P → EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hsA : ContDiffOn ℝ ∞ (Function.uncurry sourceA)
      ((U) ×ˢ univ))
    (hsf : ContDiffOn ℝ ∞ (Function.uncurry sourcef)
      ((U) ×ˢ univ))
    (hperiodA : ∀ z ∈ U,
      ∀ (x : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ),
        sourceA z (x + toLp 2 (fun i ↦ (m i : ℝ))) = sourceA z x)
    (hperiodf : ∀ z ∈ U,
      ∀ (x : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ),
        sourcef z (x + toLp 2 (fun i ↦ (m i : ℝ))) = sourcef z x)
    (hAvalue : ∀ z ∈ U,
      ∀ (u : LittlePeriodicCAlphaFunction a M 2 α) x,
        (A z u).val.toFun x = sourceA z x (u.val.toFun x))
    (hfvalue : ∀ z ∈ U, ∀ x,
      (f z).val.toFun x = sourcef z x)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ContDiffOn ℝ ∞ f U ∧ ContDiffOn ℝ ∞ A U ∧
      ContDiffOn ℝ ∞ (fun z : P × EuclideanSpace ℝ (Fin a) ↦
        littlePeriodicCAlphaTranslateIsometry z.2 (f z.1)) (U ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun z : P × EuclideanSpace ℝ (Fin a) ↦
        (littlePeriodicCAlphaTranslateIsometry z.2).toContinuousLinearMap.comp
          ((A z.1).comp
            (littlePeriodicCAlphaTranslateIsometry (-z.2)).toContinuousLinearMap)) (U ×ˢ univ) := by
  let e : (P) ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (P))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let W := e.symm ⁻¹' U
  have hW : IsOpen W := hU.preimage e.symm.continuous
  let ca := fun p x ↦ sourceA (e.symm p) x
  let cf := fun p x ↦ sourcef (e.symm p) x
  have hin : ContDiff ℝ ∞ (fun z :
      EuclideanSpace ℝ (Fin (Module.finrank ℝ (P))) ×
        EuclideanSpace ℝ (Fin a) ↦ (e.symm z.1, z.2)) :=
    (e.symm.contDiff.comp contDiff_fst).prodMk contDiff_snd
  have hca : ContDiffOn ℝ ∞ (Function.uncurry ca) (W ×ˢ univ) :=
    hsA.comp hin.contDiffOn (fun z hz ↦ ⟨hz.1, hz.2⟩)
  have hcf : ContDiffOn ℝ ∞ (Function.uncurry cf) (W ×ˢ univ) :=
    hsf.comp hin.contDiffOn (fun z hz ↦ ⟨hz.1, hz.2⟩)
  obtain ⟨fe, Ae, hfe, hAe, hfet, hAet⟩ := balanced_fixed_translated_data W hW ca cf
    hca hcf (fun p hp x m ↦ hperiodA (e.symm p) hp x m)
    (fun p hp x m ↦ hperiodf (e.symm p) hp x m) hα0 hα1
  have hforce (z : P) (hz : z ∈ U) : fe (e z) = f z := by
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext x
    have h := hfe (e z) (by simpa only [W, mem_preimage, e.symm_apply_apply] using hz) x
    simp only [cf, e.symm_apply_apply] at h
    exact h.trans (hfvalue z hz x).symm
  have hops (z : P) (hz : z ∈ U) : Ae (e z) = A z := by
    apply DFunLike.coe_injective
    funext u
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext x
    have h := hAe (e z) (by simpa only [W, mem_preimage, e.symm_apply_apply] using hz) u x
    simp only [ca, e.symm_apply_apply] at h
    exact h.trans (hAvalue z hz u x).symm
  have hout : ContDiff ℝ ∞ (fun z : (P) × EuclideanSpace ℝ (Fin a) ↦
      (e z.1, z.2)) := (e.contDiff.comp contDiff_fst).prodMk contDiff_snd
  have hmap : MapsTo (fun z : (P) × EuclideanSpace ℝ (Fin a) ↦ (e z.1, z.2))
      (U ×ˢ univ) (W ×ˢ univ) := by
    intro z hz
    exact ⟨by simpa only [W, mem_preimage, e.symm_apply_apply] using hz.1, hz.2⟩
  have hfτ : ContDiffOn ℝ ∞ (fun z : (P) × EuclideanSpace ℝ (Fin a) ↦
      littlePeriodicCAlphaTranslateIsometry z.2 (f z.1)) (U ×ˢ univ) := by
    apply (hfet.comp hout.contDiffOn hmap).congr
    intro z hz
    dsimp only [Function.comp_apply]
    rw [hforce z.1 hz.1]
  have hAτ : ContDiffOn ℝ ∞ (fun z : (P) × EuclideanSpace ℝ (Fin a) ↦
      (littlePeriodicCAlphaTranslateIsometry z.2).toContinuousLinearMap.comp
        ((A z.1).comp
          (littlePeriodicCAlphaTranslateIsometry (-z.2)).toContinuousLinearMap))
      (U ×ˢ univ) := by
    apply (hAet.comp hout.contDiffOn hmap).congr
    intro z hz
    dsimp only [Function.comp_apply]
    rw [hops z.1 hz.1]
  have hzero {d : ℕ} (u : LittlePeriodicCAlphaFunction a d 2 α) :
      littlePeriodicCAlphaTranslateIsometry 0 u = u := by
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext x
    change u.val.toFun (x + 0) = u.val.toFun x
    rw [add_zero]
  have hinc : ContDiff ℝ ∞ (fun p : P ↦
      (p, (0 : EuclideanSpace ℝ (Fin a)))) := contDiff_id.prodMk contDiff_const
  have hf : ContDiffOn ℝ ∞ f U := by
    apply (hfτ.comp hinc.contDiffOn (fun p hp ↦ ⟨hp, mem_univ _⟩)).congr
    intro p hp
    exact (hzero (f p)).symm
  have hA : ContDiffOn ℝ ∞ A U := by
    apply (hAτ.comp hinc.contDiffOn (fun p hp ↦ ⟨hp, mem_univ _⟩)).congr
    intro p hp
    symm
    apply DFunLike.coe_injective
    funext u
    change littlePeriodicCAlphaTranslateIsometry 0
      (A p (littlePeriodicCAlphaTranslateIsometry (-0) u)) = A p u
    rw [neg_zero, hzero, hzero]
  exact ⟨hf, hA, hfτ, hAτ⟩

#print axioms balanced_fixed_translated_source_data

end GlobalEmbedding.Paper
