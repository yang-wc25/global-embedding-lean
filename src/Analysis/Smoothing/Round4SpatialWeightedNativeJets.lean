import Smoothing.IntegrationSpatialWeightedGain
import Smoothing.IntegrationSpatialModelNorms
import Smoothing.Round3OuterShiftedNativeJets

/-!
# Native spatial value, first derivative and Hessian from the literal norm

The fixed linear coordinate changes preserve the actual map. No pure
parameter derivative is inserted into the base input. All further joint
jets carry their original ell^k weights.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace
section Native
variable {Ep Es Y : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {n d q : ℕ}

theorem round4SpatialWeighted_native_model_jet_le
    {ι : Type*} [Fintype ι]
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ))
    (u : ι → Ep × Es → Y) (O S : ι → Set (Ep × Es))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (O i))
    (j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hFinite : parameterSpatialWeighted (n := n) (d := d) j ell
      (parameterModelCoordinates cp cs cy u) (parameterModelDomains cp cs O)
      (parameterModelDomains cp cs S) ≠ ⊤)
    (i : ι) (k : ℕ) (hk : k ≤ j) (z : Ep × Es) (hz : z ∈ S i) :
    ell^k * ‖iteratedFDeriv ℝ k (spatialNativeJet (u i)) z‖ ≤
      parameterModelNativeFactor cp cs cy j *
        (parameterSpatialWeighted (n := n) (d := d) j ell
          (parameterModelCoordinates cp cs cy u) (parameterModelDomains cp cs O)
          (parameterModelDomains cp cs S)).toReal := by
  let c := parameterJointModel cp cs
  have hO' (a : ι) : IsOpen (parameterModelDomains cp cs O a) := (hO a).preimage c.symm.continuous
  have hS' (a : ι) : parameterModelDomains cp cs S a ⊆ parameterModelDomains cp cs O a :=
    fun _ hx => hSO a hx
  have hz' : sourceFirstCoordinates n d ((cp.prodCongr cs) z) ∈ parameterModelDomains cp cs S i := by
    simpa [parameterModelDomains, parameterJointModel] using hz
  have hn := parameterSpatialWeighted_native_jet_le j ell hell
    (parameterModelCoordinates cp cs cy u) (parameterModelDomains cp cs O)
    (parameterModelDomains cp cs S) hO' hS'
    (parameterModelCoordinates_contDiffOn cp cs cy u O hu) hFinite i hk le_rfl hz'
  rw [parameterModelCoordinates_native] at hn
  have hr := norm_iteratedFDeriv_spatial_model_change_reverse cp cs cy (u i) k z
  let A := ‖(spatialJetModelEquiv cs.symm cy.symm).toContinuousLinearMap‖
  have hA : 0 ≤ A := norm_nonneg _
  have hcost : A * linearModelFactor (cp.prodCongr cs) k ≤
      A * linearModelFactor (cp.prodCongr cs) j :=
    mul_le_mul_of_nonneg_left (linearModelFactor_mono _ hk) hA
  have hh := mul_le_mul hcost hn
    (mul_nonneg (pow_nonneg hell.le k) (norm_nonneg _))
    (mul_nonneg hA (linearModelFactor_nonneg _ _))
  have hs := mul_le_mul_of_nonneg_left hr (pow_nonneg hell.le k)
  convert hs.trans (by simpa only [mul_assoc, mul_left_comm (ell^k)] using hh) using 1 <;>
    unfold parameterModelNativeFactor <;> ring

end Native

variable {n d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es

/-- The original native chart map is the same map in the fixed model. -/
theorem round4_original_spatial_weighted_native_jets
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) (F : P × M → Ey)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hF : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i))
    (j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hFinite : parameterSpatialWeighted (n := n) (d := d) j ell
      (incrementsOriginalMapCoordinates A B F) (incrementsOriginalDifferentiation A B) S ≠ ⊤)
    (R : ℝ) (hR : (parameterSpatialWeighted (n := n) (d := d) j ell
      (incrementsOriginalMapCoordinates A B F) (incrementsOriginalDifferentiation A B) S).toReal ≤ R)
    (i : Fin A.count × Fin c) (k : ℕ) (hk : k ≤ j) (z : X)
    (hz : parameterTensorModelEquiv n d z ∈ S i) :
    ell^k*‖iteratedFDeriv ℝ k (spatialNativeJet (round3OriginalNativeMapCoordinates A B F i)) z‖ ≤
      parameterModelNativeFactor (EuclideanSpace.equiv (Fin d) ℝ)
        (EuclideanSpace.equiv (Fin n) ℝ) (EuclideanSpace.equiv (Fin N) ℝ) j * R := by
  let cp := EuclideanSpace.equiv (Fin d) ℝ
  let cs := EuclideanSpace.equiv (Fin n) ℝ
  let cy := EuclideanSpace.equiv (Fin N) ℝ
  let f := round3OriginalNativeMapCoordinates A B F
  let O := fun i => (parameterTensorModelEquiv n d) ⁻¹' incrementsOriginalDifferentiation A B i
  let Z := fun i => (parameterTensorModelEquiv n d) ⁻¹' S i
  have hO : ∀ i, IsOpen (O i) := fun i =>
    (parameterRound2_originalDifferentiation_open A B i).preimage (parameterTensorModelEquiv n d).continuous
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) := by
    intro i
    rw [show f i = cy.symm ∘ incrementsOriginalMapCoordinates A B F i ∘ parameterTensorModelEquiv n d from
      round3_original_native_map_coordinates_eq A B F i]
    exact cy.symm.contDiff.comp_contDiffOn
      ((hF i).comp (parameterTensorModelEquiv n d).contDiff.contDiffOn (fun _ hx => hx))
  have hfEq : parameterModelCoordinates cp cs cy f = incrementsOriginalMapCoordinates A B F := by
    funext a y
    rfl
  have hOEq : parameterModelDomains cp cs O = incrementsOriginalDifferentiation A B := by
    funext a
    ext y
    change (parameterTensorModelEquiv n d) ((parameterTensorModelEquiv n d).symm y) ∈
      incrementsOriginalDifferentiation A B a ↔ y ∈ incrementsOriginalDifferentiation A B a
    simp only [ContinuousLinearEquiv.apply_symm_apply]
  have hZEq : parameterModelDomains cp cs Z = S := by
    funext a
    ext y
    change (parameterTensorModelEquiv n d) ((parameterTensorModelEquiv n d).symm y) ∈ S a ↔ y ∈ S a
    simp only [ContinuousLinearEquiv.apply_symm_apply]
  have hfin : parameterSpatialWeighted (n := n) (d := d) j ell
      (parameterModelCoordinates cp cs cy f) (parameterModelDomains cp cs O)
      (parameterModelDomains cp cs Z) ≠ ⊤ := by rw [hfEq,hOEq,hZEq]; exact hFinite
  have h := round4SpatialWeighted_native_model_jet_le cp cs cy f O Z hO
    (fun a _ ha => hSO a ha) hf j ell hell hfin i k hk z hz
  rw [hfEq,hOEq,hZEq] at h
  exact h.trans (mul_le_mul_of_nonneg_left hR (parameterModelNativeFactor_nonneg cp cs cy j))

#print axioms round4SpatialWeighted_native_model_jet_le
#print axioms round4_original_spatial_weighted_native_jets
end GlobalEmbedding.Continuation
