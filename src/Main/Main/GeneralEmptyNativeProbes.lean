import Main.GeneralNativeProbeConstruction
import Main.EmptyNativeProbes

/-!
# The unrestricted legal-wave input on an empty source

The original source and finite wave list may both be empty, independently.
Unlike the frozen bump class, a general legal wave has no chosen center and
may exist on an empty source even when the original label count is positive.
This construction handles every supplied label and atlas, preserving all
original norms. It does not use impossible-wave elimination.
-/
noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Upgrade GlobalEmbedding.NormalPolar GlobalEmbedding.Main
variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [IsEmpty M]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,E)

/-- Genuine native data on the same reference map, arbitrary given atlas,
and arbitrary given finite wave family. The actual C² reserve is zero. -/
def generalNativeProbeData_of_isEmpty
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ,V) ∞ F₀)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F₀ x))
    {r : ℕ} (waves : Fin r → OpenSupportedLegalWave F₀ hF₀) :
    GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves where
  radius := 1
  radius_pos := zero_lt_one
  threshold := 1
  threshold_pos := zero_lt_one
  map := fun _ _ => F₀
  slice_smooth := fun _ _ => hF₀
  immersion := fun _ _ => hi₀
  joint_smooth := by
    intro t ht htt z hz
    exact isEmptyElim z.2
  metric := by
    intro t ht htt u hu x
    rfl
  weight := fun _ => 1
  weight_pos := fun _ => zero_lt_one
  distinct_on_overlap := by
    intro l k hlk hoverlap
    exact isEmptyElim hoverlap.choose
  constant := 0
  constant_nonneg := le_rfl
  etaH := fun _ => 0
  etaV := fun _ => 0
  etaH_nonneg := fun _ => le_rfl
  etaV_nonneg := fun _ => le_rfl
  etaH_tendsto := tendsto_const_nhds
  etaV_tendsto := tendsto_const_nhds
  closeness := by
    intro t ht htt u hu
    rw [probeAtlasCj_eq_zero_of_isEmpty]
    exact bot_le
  spatial_C3 := by
    intro t ht htt u hu
    rw [probeAtlasCj_eq_zero_of_isEmpty]
    exact bot_le
  parameter_C1 := by
    intro t ht htt u hu d
    rw [probeAtlasCj_eq_zero_of_isEmpty]
    exact bot_le
  parameter_C2 := by
    intro t ht htt u hu d
    rw [probeAtlasCj_eq_zero_of_isEmpty]
    exact bot_le
  native_hessian_response := by
    intro t ht htt u hu l b i x hx
    exact isEmptyElim x
  value_response := by
    intro t ht htt u hu l b x
    exact isEmptyElim x
  reserve := 0
  reserve_lt_one := zero_lt_one
  closeness_reserve := by
    intro t ht htt
    refine ⟨0,le_rfl,?_,?_⟩
    · intro u hu
      rw [probeAtlasCj_eq_zero_of_isEmpty]
      exact bot_le
    · simp only [mul_zero,le_refl]


/-- The full exact paired family in the empty-source branch for any original
finite list of arbitrary smooth-cutoff waves. -/
def generalExactProbeFamily_of_isEmpty [T2Space M]
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ,V) ∞ F₀)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F₀ x))
    {r : ℕ} (waves : Fin r → OpenSupportedLegalWave F₀ hF₀) :
    GeneralExactProbeFamily F₀ hF₀ A waves :=
  (generalNativeProbeData_of_isEmpty F₀ hF₀ A hA hcompact hcover hi₀ waves).toGeneralExactProbeFamily

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.generalNativeProbeData_of_isEmpty
#print axioms GlobalEmbedding.Continuation.generalExactProbeFamily_of_isEmpty
