import NormalPolar.ParameterDisplacementNorms
import NormalPolar.ParameterDisplacementFirstIncrementJets

/-!
# Complete first-increment jets in the original spatial C1/C2/C3 norms

This is the original componentwise atlas gauge on its actual support sets.
The native weighted jets are converted without changing the charts, the
function, or the parameter norm. Lower-order terms remain in every Cj norm.
-/

noncomputable section
open Manifold Set GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff ENNReal
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade GlobalEmbedding.Continuation

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Chartwise smoothness of the literal same map suffices for the original
norm conversion. This avoids asking for an unrelated global extension. -/
theorem probeAtlasCj_le_of_native_chart_jets
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V)
    (hchart : ∀ i, ContDiffOn ℝ ∞ (F ∘ (A.chart i).symm) (A.chart i).target)
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
    apply v.contDiff.comp_contDiffOn
    exact (hchart i).comp e.symm.contDiff.contDiffOn (by
      rintro y ⟨z,hz,rfl⟩
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hz)
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
      _ = _ := by unfold probeAtlasFromNativeConstant; dsimp only [e,v]; ring

/-- All lower source jets are paid for by the same fast-scale budget,
because the fixed fast scale is at most one. -/
theorem probeAtlasCj_le_of_native_chart_weighted_jets
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V)
    (hchart : ∀ i, ContDiffOn ℝ ∞ (F ∘ (A.chart i).symm) (A.chart i).target)
    (j : ℕ) (tau delta B : ℝ) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hdelta : 0 ≤ delta) (hB : 0 ≤ B)
    (hjets : ∀ i, ∀ k ≤ j, ∀ x ∈ A.support i,
      tau ^ k * ‖iteratedFDeriv ℝ k (F ∘ (A.chart i).symm) (A.chart i x)‖ ≤ B * delta * tau) :
    probeAtlasCj A j F ≤
      ENNReal.ofReal (probeAtlasFromNativeConstant n N j * (B * delta * tau / tau ^ j)) := by
  apply probeAtlasCj_le_of_native_chart_jets A hA F hchart j (by positivity)
  intro i k hk x hx
  apply (le_div_iff₀ (pow_pos htau j)).mpr
  have hpow : tau ^ j ≤ tau ^ k := pow_le_pow_of_le_one htau.le htau1 hk
  calc
    _ = tau ^ j * ‖iteratedFDeriv ℝ k (F ∘ (A.chart i).symm) (A.chart i x)‖ := by ring
    _ ≤ tau ^ k * ‖iteratedFDeriv ℝ k (F ∘ (A.chart i).symm) (A.chart i x)‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ _ := hjets i k hk x hx

/-- The exact original C1, C2 and C3 rates of the entire first increment,
including every lower derivative in each norm. -/
theorem probeAtlas_low_three_of_native_chart_weighted_jets
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V)
    (hchart : ∀ i, ContDiffOn ℝ ∞ (F ∘ (A.chart i).symm) (A.chart i).target)
    (tau delta B : ℝ) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hdelta : 0 ≤ delta) (hB : 0 ≤ B)
    (hjets : ∀ i, ∀ k ≤ 3, ∀ x ∈ A.support i,
      tau ^ k * ‖iteratedFDeriv ℝ k (F ∘ (A.chart i).symm) (A.chart i x)‖ ≤ B * delta * tau) :
    probeAtlasCj A 1 F ≤ ENNReal.ofReal (probeAtlasFromNativeConstant n N 1 * B * delta) ∧
    probeAtlasCj A 2 F ≤ ENNReal.ofReal (probeAtlasFromNativeConstant n N 2 * B * delta / tau) ∧
    probeAtlasCj A 3 F ≤ ENNReal.ofReal (probeAtlasFromNativeConstant n N 3 * B * delta / tau ^ 2) := by
  have hbound (j : ℕ) (hj : j ≤ 3) := probeAtlasCj_le_of_native_chart_weighted_jets
    A hA F hchart j tau delta B htau htau1 hdelta hB
      (fun i k hk x hx => hjets i k (hk.trans hj) x hx)
  have h1 : probeAtlasFromNativeConstant n N 1 * (B * delta * tau / tau ^ 1) =
      probeAtlasFromNativeConstant n N 1 * B * delta := by field_simp
  have h2 : probeAtlasFromNativeConstant n N 2 * (B * delta * tau / tau ^ 2) =
      probeAtlasFromNativeConstant n N 2 * B * delta / tau := by field_simp
  have h3 : probeAtlasFromNativeConstant n N 3 * (B * delta * tau / tau ^ 3) =
      probeAtlasFromNativeConstant n N 3 * B * delta / tau ^ 2 := by field_simp
  exact ⟨by simpa only [h1] using hbound 1 (by omega),
    by simpa only [h2] using hbound 2 (by omega),
    by simpa only [h3] using hbound 3 (by omega)⟩

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.probeAtlasCj_le_of_native_chart_weighted_jets
#print axioms GlobalEmbedding.NormalPolar.probeAtlas_low_three_of_native_chart_weighted_jets
