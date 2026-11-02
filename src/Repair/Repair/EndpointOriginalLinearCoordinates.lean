import Repair.EndpointCoefficientProfiles

/-! Exact original full-joint coordinate convention.  Its source projection
is continuous linear, with its genuine operator norm retained in all jets. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

def repairOriginalSourceProjection (n d : ℕ) :
    (Fin (n+d) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n))).comp
    (parameterTensorModelEquiv n d).symm.toContinuousLinearMap

@[simp] theorem repairOriginalSourceProjection_apply (n d : ℕ) (y : Fin (n+d) → ℝ) :
    repairOriginalSourceProjection n d y = incrementsOriginalSourcePoint y := rfl

theorem repair_linear_right_jet
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (g : X →L[ℝ] Y) (f : Y → Z) (O : Set Y) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (x : X) (hx : g x ∈ O) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (f ∘ g) x‖ ≤ ‖iteratedFDeriv ℝ j f (g x)‖*‖g‖^j := by
  have hpre : IsOpen (g ⁻¹' O) := hO.preimage g.continuous
  have he := g.iteratedFDerivWithin_comp_right hf hO.uniqueDiffOn hpre.uniqueDiffOn hx
    (i := j) (by simp)
  rw [iteratedFDerivWithin_of_isOpen j hpre hx,
    iteratedFDerivWithin_of_isOpen j hO hx] at he
  rw [he]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ j f (g x)) (fun _ : Fin j => g))

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,D)

theorem repair_actual_original_linear_coordinates
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hAtlas : IsSmoothBufferedAtlas Data.atlas)
    (nu : Fin Data.primaryCount)
    (owner : OpenPartialHomeomorph M D)
    (howner : owner ∈ IsManifold.maximalAtlas IT ∞ M)
    (template : ActualGoodDictionaryTemplate D V)
    (a : EdgePair (Module.finrank ℝ D+1))
    (hL : ∀ p x, Data.linearArgument nu p x =
      repairHostTemplateArgument owner howner template a x)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (y : Fin (m+1+d) → ℝ)
    (hy : incrementsOriginalSourcePoint y ∈ ((Data.atlas.chart i.1).symm.trans owner).source) :
    incrementsOriginalLinearArgumentCoordinates Data nu i y =
      repairTemplateCoordinateVector template a
        (repairActualObserverJacobian owner (Data.atlas.chart i.1)
          (incrementsOriginalSourcePoint y)) := by
  ext k
  unfold incrementsOriginalLinearArgumentCoordinates
  rw [hL]
  dsimp only [incrementsOriginalJointPoint]
  have hown : (Data.atlas.chart i.1).symm (incrementsOriginalSourcePoint y) ∈ owner.source := hy.2
  have hobs := (Data.atlas.chart i.1).map_target hy.1
  rw [repair_host_template_actual_coordinate_tensor Data owner howner template a i.1 _ hown]
  rw [repair_actual_coefficient_jacobian Data hAtlas owner howner i.1 _ hown hobs]
  rfl

theorem repair_actual_original_linear_coordinates_smooth
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hAtlas : IsSmoothBufferedAtlas Data.atlas)
    (nu : Fin Data.primaryCount)
    (owner : OpenPartialHomeomorph M D)
    (howner : owner ∈ IsManifold.maximalAtlas IT ∞ M)
    (template : ActualGoodDictionaryTemplate D V)
    (a : EdgePair (Module.finrank ℝ D+1))
    (hL : ∀ p x, Data.linearArgument nu p x =
      repairHostTemplateArgument owner howner template a x)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    ContDiffOn ℝ ∞ (incrementsOriginalLinearArgumentCoordinates Data nu i)
      ((repairOriginalSourceProjection (m+1) d) ⁻¹'
        ((Data.atlas.chart i.1).symm.trans owner).source) := by
  have hs := repair_template_coordinate_vector_smooth template a _ _
    (repair_actual_observer_jacobian_smooth owner (Data.atlas.chart i.1)
      howner (hAtlas.chart_mem i.1))
  apply (hs.comp_continuousLinearMap (repairOriginalSourceProjection (m+1) d)).congr
  intro y hy
  exact repair_actual_original_linear_coordinates Data hAtlas nu owner howner template a hL i y hy

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_actual_original_linear_coordinates
#print axioms GlobalEmbedding.Continuation.repair_actual_original_linear_coordinates_smooth
