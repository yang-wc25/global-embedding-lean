import Upgrade.CompactFixedAtlasRank
import Upgrade.ProtectionSupported
import GlobalEmbedding.Offline.CoincidenceAvoidanceEmbedding

/-!
# Original C² full-rank protection through exact metric perturbations

The compact buffer after rank-q removal has actual surjective true second
form. An original-C² tolerance protects this property for the later same-
metric maps. Immersion of the new map is derived from its exact original
metric, so no new-map rank or differential injectivity is an assumption.
-/

noncomputable section
open Set Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M] [T2Space M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem exists_originalC2_sameMetric_fullRank_reserve
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ A.support i) (hdim : 2 ≤ n) (hcodim : n < N)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) {C : Set M} (hC : IsCompact C)
    (hfull : ∀ x ∈ C, Function.Surjective (trueSecondForm F hF x)) :
    ∃ e > 0, ∀ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) →
      probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal e →
      ∀ x ∈ C, Function.Surjective (trueSecondForm G hG x) := by
  have hhigh : ∀ x ∈ C, N - n - 1 < finrank ℝ (trueSecondForm F hF x).range := by
    intro x hx
    have h := (trueSecondForm_surjective_iff_finrank_ge F hF x (himm x)).mp (hfull x hx)
    rw [finrank_euclideanSpace_fin] at h
    omega
  obtain ⟨e, he, hreserve⟩ := exists_originalC2_rank_reserve A hA hcompact hcoverA hdim
    F hF himm hphase (N - n - 1) hC hhigh
  refine ⟨e, he, ?_⟩
  intro G hG hmetric hsmall x hx
  have himmG := immersion_of_inducedMetric_eq F G x (hmetric x) (himm x)
  apply (trueSecondForm_surjective_iff_finrank_ge G hG x himmG).mpr
  rw [finrank_euclideanSpace_fin]
  have h := hreserve G hG hsmall x hx
  omega

end GlobalEmbedding.Upgrade
