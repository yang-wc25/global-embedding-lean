import Smoothing.IntegrationSpatialWeightedGain

/-!
# Actual source, parameter and target model transport of spatial jets

Continuous linear equivalences transport the true spatial two-jet, including
both source tangent slots. The equivalences need not be isometries. In
particular Euclidean/Pi conversion is handled with both actual operator norms.
The identities hold for native totalized derivatives because all model changes
are invertible; no unjustified derivative linearity is used.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff

namespace GlobalEmbedding.Continuation

variable {Ep Es Y Ep' Es' Y' : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup Ep'] [NormedSpace ℝ Ep']
  [NormedAddCommGroup Es'] [NormedSpace ℝ Es'] [FiniteDimensional ℝ Es']
  [NormedAddCommGroup Y'] [NormedSpace ℝ Y'] [FiniteDimensional ℝ Y']

attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

/-- Both spatial derivative slots are transformed by the same genuine
source model equivalence, and the target is transformed at every order. -/
def spatialJetModelEquiv (cs : Es ≃L[ℝ] Es') (cy : Y ≃L[ℝ] Y') :
    SpatialNativeJet Es Y ≃L[ℝ] SpatialNativeJet Es' Y' :=
  cy.prodCongr ((cs.arrowCongr cy).prodCongr (cs.arrowCongr (cs.arrowCongr cy)))

/-- Actual first derivative under invertible source and target conversions. -/
theorem fderiv_model_conjugate (cs : Es ≃L[ℝ] Es') (cy : Y ≃L[ℝ] Y')
    (f : Es → Y) (x : Es') :
    fderiv ℝ (cy ∘ f ∘ cs.symm) x = (cs.arrowCongr cy) (fderiv ℝ f (cs.symm x)) := by
  rw [cy.comp_fderiv, cs.symm.comp_right_fderiv]
  rfl

/-- The true second derivative is conjugated in both source slots. -/
theorem second_fderiv_model_conjugate (cs : Es ≃L[ℝ] Es') (cy : Y ≃L[ℝ] Y')
    (f : Es → Y) (x : Es') :
    fderiv ℝ (fderiv ℝ (cy ∘ f ∘ cs.symm)) x =
      (cs.arrowCongr (cs.arrowCongr cy)) (fderiv ℝ (fderiv ℝ f) (cs.symm x)) := by
  have h : fderiv ℝ (cy ∘ f ∘ cs.symm) =
      (cs.arrowCongr cy) ∘ fderiv ℝ f ∘ cs.symm := funext (fderiv_model_conjugate cs cy f)
  rw [h]
  exact fderiv_model_conjugate cs (cs.arrowCongr cy) (fderiv ℝ f) x

/-- The transformed field is the jet of the transformed actual function. -/
theorem spatialNativeJet_model_change (cp : Ep ≃L[ℝ] Ep') (cs : Es ≃L[ℝ] Es')
    (cy : Y ≃L[ℝ] Y') (u : Ep × Es → Y) (z : Ep' × Es') :
    spatialNativeJet (fun y => cy (u (cp.symm y.1, cs.symm y.2))) z =
      spatialJetModelEquiv cs cy (spatialNativeJet u (cp.symm z.1, cs.symm z.2)) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · exact fderiv_model_conjugate cs cy (fun x => u (cp.symm z.1, x)) z.2
  · exact second_fderiv_model_conjugate cs cy (fun x => u (cp.symm z.1, x)) z.2

theorem spatialNativeJet_model_change_eq (cp : Ep ≃L[ℝ] Ep') (cs : Es ≃L[ℝ] Es')
    (cy : Y ≃L[ℝ] Y') (u : Ep × Es → Y) :
    spatialNativeJet (cy ∘ u ∘ (cp.prodCongr cs).symm) =
      spatialJetModelEquiv cs cy ∘ spatialNativeJet u ∘ (cp.prodCongr cs).symm :=
  funext (spatialNativeJet_model_change cp cs cy u)

/-- Exact all-order derivative bound under genuine source/parameter/target
model conversion, with the actual operator norms retained. -/
theorem norm_iteratedFDeriv_spatial_model_change
    (cp : Ep ≃L[ℝ] Ep') (cs : Es ≃L[ℝ] Es') (cy : Y ≃L[ℝ] Y')
    (u : Ep × Es → Y) (j : ℕ) (z : Ep' × Es') :
    ‖iteratedFDeriv ℝ j (spatialNativeJet (cy ∘ u ∘ (cp.prodCongr cs).symm)) z‖ ≤
      (‖(spatialJetModelEquiv cs cy).toContinuousLinearMap‖ *
        linearModelFactor (cp.prodCongr cs).symm j) *
          ‖iteratedFDeriv ℝ j (spatialNativeJet u) ((cp.prodCongr cs).symm z)‖ := by
  rw [spatialNativeJet_model_change_eq cp cs cy u,
    (spatialJetModelEquiv cs cy).iteratedFDeriv_comp_left]
  have hn := (spatialJetModelEquiv cs cy).toContinuousLinearMap.norm_compContinuousMultilinearMap_le
    (iteratedFDeriv ℝ j (spatialNativeJet u ∘ (cp.prodCongr cs).symm) z)
  apply hn.trans
  have ht := norm_iteratedFDeriv_comp_equiv_le (cp.prodCongr cs).symm (spatialNativeJet u) j z
  have hh := mul_le_mul_of_nonneg_left ht (spatialJetModelEquiv cs cy).toContinuousLinearMap.opNorm_nonneg
  convert hh using 1 <;> ring

/-- Reverse transport gives an actual bound for the original native jet;
it does not silently identify Euclidean and coordinate sup norms. -/
theorem norm_iteratedFDeriv_spatial_model_change_reverse
    (cp : Ep ≃L[ℝ] Ep') (cs : Es ≃L[ℝ] Es') (cy : Y ≃L[ℝ] Y')
    (u : Ep × Es → Y) (j : ℕ) (z : Ep × Es) :
    ‖iteratedFDeriv ℝ j (spatialNativeJet u) z‖ ≤
      (‖(spatialJetModelEquiv cs.symm cy.symm).toContinuousLinearMap‖ *
        linearModelFactor (cp.prodCongr cs) j) *
          ‖iteratedFDeriv ℝ j
            (spatialNativeJet (cy ∘ u ∘ (cp.prodCongr cs).symm)) ((cp.prodCongr cs) z)‖ := by
  have h := norm_iteratedFDeriv_spatial_model_change cp.symm cs.symm cy.symm
    (cy ∘ u ∘ (cp.prodCongr cs).symm) j z
  have he : cy.symm ∘ (cy ∘ u ∘ (cp.prodCongr cs).symm) ∘
      (cp.symm.prodCongr cs.symm).symm = u := by
    funext x
    simp
  rw [he] at h
  exact h

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.spatialNativeJet_model_change
#print axioms GlobalEmbedding.Continuation.norm_iteratedFDeriv_spatial_model_change_reverse
