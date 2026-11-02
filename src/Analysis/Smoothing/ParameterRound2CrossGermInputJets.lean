import Smoothing.ParameterRound2CrossGermCoordinates

/-!
# Original weighted map norms produce the actual spatial jets used by Cross

The map is literally the native F in the original product chart. Full-joint
derivative bounds follow from the unchanged coordinate norm, with the stated
base shift. A true spatial derivative costs one shift, so base2 for the
smoothing error and base1 for the increment give the cross estimate directly.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d N pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterRound2CrossGermInputChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2CrossGermInputIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

theorem parameterRound2_original_map_weighted_source_germ_jets
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (UI : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hUI : ∀ i, IsOpen (UI i))
    (hUIO : ∀ i, UI i ⊆ incrementsOriginalDifferentiation A B i)
    (hSUI : ∀ i, S i ⊆ UI i)
    (F : P × M → Ey)
    (hF : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i) (UI i))
    (base m : ℕ) (hbase : 1 ≤ base) (tau : ℝ) (htau : 0 < tau)
    (hfinite : paperAtlasWeighted base m tau (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤) :
    ∀ i : Fin A.count × Fin pcount, ∀ k ≤ m, ∀ z : Ep × Es,
      parameterTensorModelEquiv n d z ∈ S i →
      tau^k * ‖iteratedFDeriv ℝ k (fun w : Ep × Es =>
        fderiv ℝ (fun x => F ((B i.2).symm w.1,(A.chart i.1).symm x)) w.2) z‖ ≤
      parameterRound2_mapWeightedJetCost n d N base m *
        (paperAtlasWeighted base m tau (incrementsOriginalMapCoordinates A B F)
          (incrementsOriginalDifferentiation A B) S).toReal := by
  intro i k hk z hz
  let f := fun z : Ep × Es => F ((B i.2).symm z.1,(A.chart i.1).symm z.2)
  let O := (parameterTensorModelEquiv n d) ⁻¹' UI i
  have hO : IsOpen O := (hUI i).preimage (parameterTensorModelEquiv n d).continuous
  have hf : ContDiffOn ℝ ∞ f O := parameterRound2_nativeMapChart_germ_contDiffOn A B F i (UI i) (hF i)
  have hzO : z ∈ O := hSUI i hz
  have he := actual_paperAtlasWeighted_open_restrict base m tau
    (incrementsOriginalMapCoordinates A B F) (incrementsOriginalDifferentiation A B) UI S
    (parameterRound2_originalDifferentiation_open A B) hUI hUIO hSUI
  have hfiniteUI : paperAtlasWeighted base m tau (incrementsOriginalMapCoordinates A B F) UI S ≠ ⊤ :=
    he ▸ hfinite
  have hd := spatial_first_jet_le hO hf hzO k
  have hj := paperAtlasWeighted_native_shifted_joint_jet_le (parameterTensorModelEquiv n d)
    (EuclideanSpace.equiv (Fin N) ℝ).symm base m tau htau
    (incrementsOriginalMapCoordinates A B F) UI S hUI hSUI hF
    hfiniteUI i hk hbase hz
  rw [← parameterRound2_nativeMapChart_eq_coordinate A B F i,← he] at hj
  exact (mul_le_mul_of_nonneg_left hd (pow_nonneg htau.le k)).trans hj

#print axioms parameterRound2_original_map_weighted_source_germ_jets
end
end GlobalEmbedding.Continuation
