import Upgrade.CompactFixedAtlasJets
import GlobalEmbedding.Offline.ModelCoordinateNorms

/-!
# Native displacement bounds give the original atlas norms

This is the reverse direction of the already available original-norm-to-jet
estimate. It uses the same buffered support sets, actual chart inverses and
actual Euclidean/sup-coordinate equivalences. Its constant depends only on
the fixed dimensions and derivative order, not on the number of charts.
-/

noncomputable section
open Manifold Set GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- The genuine target conversion and cumulative source conversion cost. -/
def probeAtlasFromNativeConstant (n N j : ℕ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap‖ *
    linearModelFactor (EuclideanSpace.equiv (Fin n) ℝ).symm j

theorem probeAtlasFromNativeConstant_nonneg (n N j : ℕ) :
    0 ≤ probeAtlasFromNativeConstant n N j :=
  mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _)

/-- Actual native jets of the same global map, bounded only on the original
supports, control its original coordinate norm on exactly those supports. -/
theorem probeAtlasCj_le_of_native_jets
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (j : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hjets : ∀ i, ∀ k ≤ j, ∀ x ∈ A.support i,
      ‖iteratedFDeriv ℝ k (F ∘ (A.chart i).symm) (A.chart i x)‖ ≤ B) :
    probeAtlasCj A j F ≤ ENNReal.ofReal (probeAtlasFromNativeConstant n N j * B) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let v := EuclideanSpace.equiv (Fin N) ℝ
  change paperAtlasCj j (fun i x ↦ v (F ((A.chart i).symm (e.symm x))))
    (fun i ↦ e '' (A.chart i).target)
    (fun i ↦ e '' ((A.chart i) '' A.support i)) ≤ _
  apply paperAtlasCj_le_of_jet_bound
  · intro i
    exact e.toHomeomorph.isOpenMap _ (A.chart i).open_target
  · intro i
    rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨A.chart i x, (A.chart i).map_source (hA.support_subset i hx), rfl⟩
  · intro i
    exact probeAtlas_coordinate_smooth A hA F hF i
  · intro i k hk y hy
    obtain ⟨z, ⟨x, hx, rfl⟩, rfl⟩ := hy
    change ‖iteratedFDeriv ℝ k (v ∘ ((F ∘ (A.chart i).symm) ∘ e.symm))
      (e (A.chart i x))‖ ≤ _
    rw [v.iteratedFDeriv_comp_left]
    have hs := norm_iteratedFDeriv_comp_equiv_le e.symm (F ∘ (A.chart i).symm)
      k (e (A.chart i x))
    simp only [ContinuousLinearEquiv.symm_apply_apply] at hs
    calc
      _ ≤ ‖v.toContinuousLinearMap‖ *
          ‖iteratedFDeriv ℝ k ((F ∘ (A.chart i).symm) ∘ e.symm)
            (e (A.chart i x))‖ :=
        v.toContinuousLinearMap.norm_compContinuousMultilinearMap_le _
      _ ≤ ‖v.toContinuousLinearMap‖ *
          (‖iteratedFDeriv ℝ k (F ∘ (A.chart i).symm) (A.chart i x)‖ *
            linearModelFactor e.symm k) :=
        mul_le_mul_of_nonneg_left hs (norm_nonneg _)
      _ ≤ ‖v.toContinuousLinearMap‖ * (B * linearModelFactor e.symm j) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hjets i k hk x hx) (linearModelFactor_mono e.symm hk)
            (linearModelFactor_nonneg e.symm k) hB) (norm_nonneg _)
      _ = probeAtlasFromNativeConstant n N j * B := by
        dsimp only [probeAtlasFromNativeConstant, e, v]
        ring

/-- At order one the genuine value and genuine fixed-chart first jet are
the entire input. No independent jet carrier is introduced. -/
theorem probeAtlasC1_le_of_value_firstJet
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    {B : ℝ} (hB : 0 ≤ B)
    (hvalue : ∀ i, ∀ x ∈ A.support i, ‖F x‖ ≤ B)
    (hfirst : ∀ i, ∀ x ∈ A.support i, ‖probeAtlasFirstJet A F i x‖ ≤ B) :
    probeAtlasCj A 1 F ≤ ENNReal.ofReal (probeAtlasFromNativeConstant n N 1 * B) := by
  apply probeAtlasCj_le_of_native_jets A hA F hF 1 hB
  intro i k hk x hx
  interval_cases k
  · simpa only [norm_iteratedFDeriv_zero, Function.comp_apply,
      (A.chart i).left_inv (hA.support_subset i hx)] using hvalue i x hx
  · simpa only [norm_iteratedFDeriv_one, probeAtlasFirstJet] using hfirst i x hx

end GlobalEmbedding.NormalPolar
