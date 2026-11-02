import Repair.EndpointOriginalLinearCoordinates

/-! Original full-joint linear coefficient estimates.  The named costs read
the original transition profiles only through j+1 and retain the exact
Fin(n+d) sup-norm to Euclidean-source comparison. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle Function Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

def repairOriginalJointLinearProfile (n d : ℕ) (A : ℝ) (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  repairOriginalLinearProfile A T j * ‖repairOriginalSourceProjection n d‖^j

theorem repairOriginalJointLinearProfile_nonneg (n d : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (T : ℕ → ℝ) (j : ℕ) : 0 ≤ repairOriginalJointLinearProfile n d A T j := by
  unfold repairOriginalJointLinearProfile repairOriginalLinearProfile
  positivity

theorem repairOriginalJointLinearProfile_prefix (n d : ℕ) (A : ℝ) (T U : ℕ → ℝ)
    (j : ℕ) (h : ∀ k ≤ j+1, T k = U k) :
    repairOriginalJointLinearProfile n d A T j = repairOriginalJointLinearProfile n d A U j := by
  unfold repairOriginalJointLinearProfile
  rw [repairOriginalLinearProfile_prefix A T U j h]

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,D)
private local instance originalLinearJetTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance originalLinearJetTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance

theorem repair_actual_original_linear_jet
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hAtlas : IsSmoothBufferedAtlas Data.atlas)
    (nu : Fin Data.primaryCount)
    (owner : OpenPartialHomeomorph M D)
    (howner : owner ∈ IsManifold.maximalAtlas IT ∞ M)
    (template : ActualGoodDictionaryTemplate D V)
    (a : EdgePair (Module.finrank ℝ D+1))
    (hL : ∀ p x, Data.linearArgument nu p x =
      repairHostTemplateArgument owner howner template a x)
    (A : ℝ) (hA : 0 ≤ A) (hCoeff : ‖template.coefficients‖ ≤ A)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (y : Fin (m+1+d) → ℝ) (j : ℕ)
    (hy : incrementsOriginalSourcePoint y ∈ ((Data.atlas.chart i.1).symm.trans owner).source)
    (hForward : ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k (owner ∘ (Data.atlas.chart i.1).symm)
        (incrementsOriginalSourcePoint y)‖ ≤ T k)
    (hInverse : ∀ k ≤ j+1,
      ‖iteratedFDeriv ℝ k (Data.atlas.chart i.1 ∘ owner.symm)
        (owner ((Data.atlas.chart i.1).symm (incrementsOriginalSourcePoint y)))‖ ≤ T k) :
    ‖iteratedFDeriv ℝ j (incrementsOriginalLinearArgumentCoordinates Data nu i) y‖ ≤
      repairOriginalJointLinearProfile (m+1) d A T j := by
  let O := ((Data.atlas.chart i.1).symm.trans owner).source
  have hO : IsOpen O := ((Data.atlas.chart i.1).symm.trans owner).open_source
  let R := repairActualObserverJacobian owner (Data.atlas.chart i.1)
  have hs : ContDiffOn ℝ ∞ R O := repair_actual_observer_jacobian_smooth owner _
    howner (hAtlas.chart_mem i.1)
  let f := fun x => repairTemplateCoordinateVector template a (R x)
  have hf : ContDiffOn ℝ ∞ f O := repair_template_coordinate_vector_smooth template a R O hs
  let L := repairOriginalSourceProjection (m+1) d
  have he : incrementsOriginalLinearArgumentCoordinates Data nu i =ᶠ[𝓝 y] f ∘ L := by
    filter_upwards [(hO.preimage L.continuous).mem_nhds hy] with z hz
    exact repair_actual_original_linear_coordinates Data hAtlas nu owner howner template a hL i z hz
  rw [(he.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
  have hbound : ‖iteratedFDeriv ℝ j f (L y)‖ ≤ repairOriginalLinearProfile A T j := by
    have hb := repair_template_coordinate_vector_scaled_jet template a A hA hCoeff
      R O hO hs j 1 (∑ k ∈ Finset.range (j+1), repairTransitionJacobianProfile T k)
      (by norm_num) (Finset.sum_nonneg (fun k _ => repairTransitionJacobianProfile_nonneg T hT k))
      (L y) hy (by
        intro k hk
        simp only [one_pow, one_mul]
        have hr := repair_actual_observer_jacobian_jet owner (Data.atlas.chart i.1)
          howner (hAtlas.chart_mem i.1) T hT k (L y) hy
          (fun l hl hlk => hForward l hl (hlk.trans hk))
          (fun l hl => hInverse l (by omega))
        exact hr.trans (Finset.single_le_sum
          (fun l _ => repairTransitionJacobianProfile_nonneg T hT l)
          (by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hk)))
    simpa only [one_pow, one_mul, repairOriginalLinearProfile, f] using hb
  exact (repair_linear_right_jet L f O hO hf y hy j).trans
    (mul_le_mul_of_nonneg_right hbound (pow_nonneg (norm_nonneg L) j))

theorem repair_original_template_linear_smooth_inputs
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hAtlas : IsSmoothBufferedAtlas Data.atlas)
    (owner : Fin Data.primaryCount → OpenPartialHomeomorph M D)
    (howner : ∀ nu, owner nu ∈ IsManifold.maximalAtlas IT ∞ M)
    (template : Fin Data.primaryCount → ActualGoodDictionaryTemplate D V)
    (a : Fin Data.primaryCount → EdgePair (Module.finrank ℝ D+1))
    (hL : ∀ nu p x, Data.linearArgument nu p x =
      repairHostTemplateArgument (owner nu) (howner nu) (template nu) (a nu) x)
    (hDomain : ∀ nu z, z ∈ Data.primaryDomain nu → z.2 ∈ (owner nu).source) :
    IncrementsOriginalLinearSmoothInputs Data := by
  constructor
  intro nu i
  apply (repair_actual_original_linear_coordinates_smooth Data hAtlas nu
    (owner nu) (howner nu) (template nu) (a nu) (hL nu) i).mono
  intro y hy
  exact ⟨hy.1.1.1, hDomain nu _ hy.1.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_actual_original_linear_jet
#print axioms GlobalEmbedding.Continuation.repair_original_template_linear_smooth_inputs
