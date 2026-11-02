import Smoothing.IntegrationSpatialModelTransport

/-!
# Literal original anisotropic norms for arbitrary genuine native models

This is the model-preserving bridge used by global smoothing. Joint
integration remains in the original Ep times Es model, and the map target
remains Y. Original scalar coordinates are only a presentation through fixed
continuous linear equivalences. Both conversion directions retain their norms.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff ENNReal

namespace GlobalEmbedding.Continuation

variable {Ep Es Y : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {n d q : ℕ}

attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

def parameterJointModel (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ)) :
    (Ep × Es) ≃L[ℝ] (Fin (n+d) → ℝ) :=
  (cp.prodCongr cs).trans (sourceFirstCoordinates n d)

def parameterModelCoordinates {ι : Type*}
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (u : ι → Ep × Es → Y) :
    ι → (Fin (n+d) → ℝ) → Fin q → ℝ :=
  fun i => cy ∘ u i ∘ (parameterJointModel cp cs).symm

def parameterModelDomains {ι : Type*}
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (O : ι → Set (Ep × Es)) : ι → Set (Fin (n+d) → ℝ) :=
  fun i => (parameterJointModel cp cs).symm ⁻¹' O i

theorem parameterModelCoordinates_native {ι : Type*}
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (u : ι → Ep × Es → Y) (i : ι) :
    parameterModelCoordinates cp cs cy u i ∘ sourceFirstCoordinates n d =
      cy ∘ u i ∘ (cp.prodCongr cs).symm := by
  funext z
  simp [parameterModelCoordinates, parameterJointModel]

theorem parameterModelCoordinates_contDiffOn {ι : Type*}
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (u : ι → Ep × Es → Y) (O : ι → Set (Ep × Es))
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (O i)) (i : ι) :
    ContDiffOn ℝ ∞ (parameterModelCoordinates cp cs cy u i) (parameterModelDomains cp cs O i) :=
  cy.contDiff.comp_contDiffOn ((hu i).comp (parameterJointModel cp cs).symm.contDiff.contDiffOn
    (fun _ h => h))

def parameterModelNativeFactor
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (j : ℕ) : ℝ :=
  ‖(spatialJetModelEquiv cs.symm cy.symm).toContinuousLinearMap‖ *
    linearModelFactor (cp.prodCongr cs) j * parameterSpatialNativeFactor n d q j

def parameterModelCoordinateFactor
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (j : ℕ) : ℝ :=
  parameterSpatialCoordinateFactor n d q j *
    (‖(spatialJetModelEquiv cs cy).toContinuousLinearMap‖ *
      linearModelFactor (cp.prodCongr cs).symm j)

theorem parameterModelNativeFactor_nonneg
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (j : ℕ) : 0 ≤ parameterModelNativeFactor cp cs cy j :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _))
    (parameterSpatialNativeFactor_nonneg _ _ _ _)

theorem parameterModelCoordinateFactor_nonneg
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (j : ℕ) : 0 ≤ parameterModelCoordinateFactor cp cs cy j :=
  mul_nonneg (parameterSpatialCoordinateFactor_nonneg _ _ _ _)
    (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _))

theorem parameterModelNativeFactor_mono
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) {k j : ℕ} (hkj : k ≤ j) :
    parameterModelNativeFactor cp cs cy k ≤ parameterModelNativeFactor cp cs cy j := by
  unfold parameterModelNativeFactor
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (linearModelFactor_mono _ hkj) (norm_nonneg _))
    (parameterSpatialNativeFactor_mono n d q hkj) (parameterSpatialNativeFactor_nonneg _ _ _ _)
    (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _))

theorem parameterModelCoordinateFactor_mono
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) {k j : ℕ} (hkj : k ≤ j) :
    parameterModelCoordinateFactor cp cs cy k ≤ parameterModelCoordinateFactor cp cs cy j := by
  unfold parameterModelCoordinateFactor
  exact mul_le_mul (parameterSpatialCoordinateFactor_mono n d q hkj)
    (mul_le_mul_of_nonneg_left (linearModelFactor_mono _ hkj) (norm_nonneg _))
    (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _))
    (parameterSpatialCoordinateFactor_nonneg _ _ _ _)

/-- Original coordinate Cj bounds the SAME native spatial jet, with all native
model and target norms retained, uniformly across the actual finite atlas. -/
theorem parameterModelCj_native_jet_le {ι : Type*} [Fintype ι]
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (j : ℕ)
    (u : ι → Ep × Es → Y) (O S : ι → Set (Ep × Es))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (O i))
    (hfinite : parameterSpatialCj (n := n) (d := d) j
      (parameterModelCoordinates cp cs cy u) (parameterModelDomains cp cs O)
      (parameterModelDomains cp cs S) ≠ ⊤)
    (i : ι) {k : ℕ} (hk : k ≤ j) {z : Ep × Es} (hz : z ∈ S i) :
    ‖iteratedFDeriv ℝ k (spatialNativeJet (u i)) z‖ ≤
      parameterModelNativeFactor cp cs cy j *
        (parameterSpatialCj (n := n) (d := d) j (parameterModelCoordinates cp cs cy u)
          (parameterModelDomains cp cs O) (parameterModelDomains cp cs S)).toReal := by
  let c := parameterJointModel cp cs
  have hO' (a : ι) : IsOpen (parameterModelDomains cp cs O a) := (hO a).preimage c.symm.continuous
  have hS' (a : ι) : parameterModelDomains cp cs S a ⊆ parameterModelDomains cp cs O a :=
    fun _ hx => hSO a hx
  have hz' : sourceFirstCoordinates n d ((cp.prodCongr cs) z) ∈ parameterModelDomains cp cs S i := by
    simpa [parameterModelDomains, parameterJointModel] using hz
  have hn := parameterSpatialCj_native_jet_le j (parameterModelCoordinates cp cs cy u)
    (parameterModelDomains cp cs O) (parameterModelDomains cp cs S) hO' hS'
    (parameterModelCoordinates_contDiffOn cp cs cy u O hu) hfinite i hk hz'
  rw [parameterModelCoordinates_native] at hn
  have hr := norm_iteratedFDeriv_spatial_model_change_reverse cp cs cy (u i) k z
  apply hr.trans
  have hcost : ‖(spatialJetModelEquiv cs.symm cy.symm).toContinuousLinearMap‖ *
      linearModelFactor (cp.prodCongr cs) k ≤
      ‖(spatialJetModelEquiv cs.symm cy.symm).toContinuousLinearMap‖ *
      linearModelFactor (cp.prodCongr cs) j :=
    mul_le_mul_of_nonneg_left (linearModelFactor_mono _ hk) (norm_nonneg _)
  have hh := mul_le_mul hcost hn (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _))
  simpa only [parameterModelNativeFactor, mul_assoc] using hh

/-- Native global jets bound the literal original coordinate norm on the
same model domains. Output non-topness is obtained before toReal. -/
theorem parameterModelCj_finite_and_bound_of_native {ι : Type*} [Fintype ι]
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (j : ℕ)
    (u : ι → Ep × Es → Y) (O S : ι → Set (Ep × Es))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (O i)) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ i, ∀ k ≤ j, ∀ z ∈ S i,
      ‖iteratedFDeriv ℝ k (spatialNativeJet (u i)) z‖ ≤ R) :
    parameterSpatialCj (n := n) (d := d) j (parameterModelCoordinates cp cs cy u)
      (parameterModelDomains cp cs O) (parameterModelDomains cp cs S) ≠ ⊤ ∧
    (parameterSpatialCj (n := n) (d := d) j (parameterModelCoordinates cp cs cy u)
      (parameterModelDomains cp cs O) (parameterModelDomains cp cs S)).toReal ≤
        parameterModelCoordinateFactor cp cs cy j * R := by
  let c := parameterJointModel cp cs
  let K := ‖(spatialJetModelEquiv cs cy).toContinuousLinearMap‖ *
    linearModelFactor (cp.prodCongr cs).symm j
  have hK : 0 ≤ K := mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _)
  have hO' (a : ι) : IsOpen (parameterModelDomains cp cs O a) := (hO a).preimage c.symm.continuous
  have hS' (a : ι) : parameterModelDomains cp cs S a ⊆ parameterModelDomains cp cs O a :=
    fun _ hx => hSO a hx
  have hb := parameterSpatialCj_finite_and_bound_of_native j (parameterModelCoordinates cp cs cy u)
    (parameterModelDomains cp cs O) (parameterModelDomains cp cs S) hO' hS'
    (parameterModelCoordinates_contDiffOn cp cs cy u O hu) (K * R) (mul_nonneg hK hR) ?_
  · refine ⟨hb.1, ?_⟩
    simpa only [parameterModelCoordinateFactor, K, mul_assoc] using hb.2
  intro i k hk z hz
  rw [parameterModelCoordinates_native]
  have hz' : (cp.prodCongr cs).symm z ∈ S i := by
    simpa [parameterModelDomains, parameterJointModel] using hz
  have hn := norm_iteratedFDeriv_spatial_model_change cp cs cy (u i) k z
  apply hn.trans
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (linearModelFactor_mono _ hk) (norm_nonneg _))
    (hbound i k hk _ hz') (norm_nonneg _) hK

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.parameterModelCj_native_jet_le
#print axioms GlobalEmbedding.Continuation.parameterModelCj_finite_and_bound_of_native
