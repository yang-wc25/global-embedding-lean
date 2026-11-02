import Smoothing.ParameterRound2CrossGermInputJets

/-!
# The true repair cross tensor in the unchanged original weighted atlas norm

The hypotheses describe the actual first spatial derivatives of the actual
two maps, and the conclusion is their native metricCrossTerm in the original
source-first coordinate norm. Every parameter derivative remains present.
The component map costs at most one; the only coordinate change cost is the
fixed model factor. No chart-count factor or squared smoothing defect occurs.
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

local instance parameterRound2CrossGermNormsChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2CrossGermNormsIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

private local instance crossNormTensorSemi : SeminormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance crossNormTensorNormed : NormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance crossNormTensorSpace : NormedSpace ℝ (Es →L[ℝ] Es →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem parameterRound2_original_metricCrossTerm_germ_weighted_norm
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A)
    (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (UI : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hUI : ∀ i, IsOpen (UI i))
    (hUIO : ∀ i, UI i ⊆ incrementsOriginalDifferentiation A B i)
    (hSUI : ∀ i, S i ⊆ UI i)
    (F U : P × M → Ey)
    (hF : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i) (UI i))
    (hU : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B U i) (UI i))
    (m : ℕ) (tau KF KU : ℝ) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hKF : 0 ≤ KF) (hKU : 0 ≤ KU)
    (hDF : ∀ i : Fin A.count × Fin pcount, ∀ k ≤ m, ∀ z : Ep × Es,
      parameterTensorModelEquiv n d z ∈ S i →
      tau^k * ‖iteratedFDeriv ℝ k (fun w : Ep × Es =>
        fderiv ℝ (fun x => F ((B i.2).symm w.1,(A.chart i.1).symm x)) w.2) z‖ ≤ KF)
    (hDU : ∀ i : Fin A.count × Fin pcount, ∀ k ≤ m, ∀ z : Ep × Es,
      parameterTensorModelEquiv n d z ∈ S i →
      tau^k * ‖iteratedFDeriv ℝ k (fun w : Ep × Es =>
        fderiv ℝ (fun x => U ((B i.2).symm w.1,(A.chart i.1).symm x)) w.2) z‖ ≤ KU) :
    let C := incrementsOriginalTensorCoordinates A B
      (fun p x => metricCrossTerm (I := 𝓘(ℝ, Es)) (fun z => F (p,z)) (fun z => U (p,z)) x)
    (∀ i, ContDiffOn ℝ ∞ (C i) (UI i)) ∧
    paperAtlasWeighted 0 m tau C (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 m tau C (incrementsOriginalDifferentiation A B) S).toReal ≤
        (m+1) * linearModelFactor (parameterTensorModelEquiv n d).symm m *
          (2^(m+1)*KF*KU) := by
  intro C
  let a := parameterTensorModelEquiv n d
  let O := fun i : Fin A.count × Fin pcount => a ⁻¹' UI i
  let S' := fun i => a ⁻¹' S i
  let DF := fun (i : Fin A.count × Fin pcount) (z : Ep × Es) =>
    fderiv ℝ (fun x => F ((B i.2).symm z.1,(A.chart i.1).symm x)) z.2
  let DU := fun (i : Fin A.count × Fin pcount) (z : Ep × Es) =>
    fderiv ℝ (fun x => U ((B i.2).symm z.1,(A.chart i.1).symm x)) z.2
  let R := fun i z => actualMetricJetPairing (DF i z) (DU i z) + actualMetricJetPairing (DU i z) (DF i z)
  let RC := fun i => parameterRound2_metricComponents n ∘ R i
  have hO : ∀ i, IsOpen (O i) := fun i => (hUI i).preimage a.continuous
  have hSO' : ∀ i, S' i ⊆ O i := fun i z hz => hSUI i hz
  have hFs (i) := parameterRound2_nativeMapChart_germ_contDiffOn A B F i (UI i) (hF i)
  have hUs (i) := parameterRound2_nativeMapChart_germ_contDiffOn A B U i (UI i) (hU i)
  have hDFs (i) : ContDiffOn ℝ ∞ (DF i) (O i) :=
    (incrementsJointSpatialJets_bridge _ (O i) (hO i)
      (hFs i)).2.1
  have hDUs (i) : ContDiffOn ℝ ∞ (DU i) (O i) :=
    (incrementsJointSpatialJets_bridge _ (O i) (hO i)
      (hUs i)).2.1
  have hRdata (i) := parameterRound2_actual_metric_cross_weighted_jets (DF i) (DU i) (O i) (S' i)
    (hO i) (hSO' i) (hDFs i) (hDUs i) m tau KF KU htau.le hKF hKU (hDF i) (hDU i)
  have hRC (i) : ContDiffOn ℝ ∞ (RC i) (O i) :=
    (parameterRound2_metricComponents n).contDiff.comp_contDiffOn (hRdata i).1
  have hRCb : ∀ i, ∀ k ≤ m, ∀ z ∈ S' i,
      tau^k * ‖iteratedFDeriv ℝ k (RC i) z‖ ≤ 2^(m+1)*KF*KU := by
    intro i k hk z hz
    have hh := slow_linear_jet_bound (parameterRound2_metricComponents n) (O i) (hO i)
      (R i) (hRdata i).1 k tau (2^(m+1)*KF*KU) htau.le z (hSO' i hz)
      ((hRdata i).2 k hk z hz)
    exact hh.trans (mul_le_of_le_one_left (by positivity) (parameterRound2_metricComponents_norm_le n))
  have hnorm := parameterRound2_paperAtlasWeighted_le_of_native_weighted_jets a m tau
    (2^(m+1)*KF*KU) htau htau1 (by positivity) RC O S' hO hSO' hRC hRCb
  have hOeq : modelCoordinateDomains a O = UI := by
    funext i
    ext y
    simp only [modelCoordinateDomains,O,Set.mem_preimage,a.apply_symm_apply]
  have hSeq : modelCoordinateDomains a S' = S := by
    funext i
    ext y
    simp only [modelCoordinateDomains,S',Set.mem_preimage,a.apply_symm_apply]
  rw [hOeq,hSeq] at hnorm
  have heqPoint (i) (y) (hy : y ∈ UI i) :
      C i y = modelCoordinateFamily a RC i y := by
    have hz : a.symm y ∈ O i := by simpa only [O,Set.mem_preimage,a.apply_symm_apply] using hy
    exact parameterRound2_metricCrossTerm_originalCoordinates_germ_eq A B hA F U i y (hUIO i hy)
      ((hFs i).contDiffAt ((hO i).mem_nhds hz)) ((hUs i).contDiffAt ((hO i).mem_nhds hz))
  have hC (i) : ContDiffOn ℝ ∞ (C i) (UI i) := by
    have hc : ContDiffOn ℝ ∞ (modelCoordinateFamily a RC i) (UI i) :=
      (hRC i).comp a.symm.contDiff.contDiffOn
        (fun y hy => by simpa only [O,Set.mem_preimage,a.apply_symm_apply] using hy)
    exact hc.congr (fun y hy => heqPoint i y hy)
  have heq : paperAtlasWeighted 0 m tau C UI S =
      paperAtlasWeighted 0 m tau (modelCoordinateFamily a RC) UI S := by
    apply paperAtlasWeighted_congr_on 0 m tau _ S hSUI
    exact heqPoint
  rw [← heq] at hnorm
  have hrestrict := actual_paperAtlasWeighted_open_restrict 0 m tau C
    (incrementsOriginalDifferentiation A B) UI S
    (parameterRound2_originalDifferentiation_open A B) hUI hUIO hSUI
  rw [← hrestrict] at hnorm
  exact ⟨hC,hnorm⟩

#print axioms parameterRound2_original_metricCrossTerm_germ_weighted_norm
end
end GlobalEmbedding.Continuation
