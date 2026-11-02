import Smoothing.Round3OuterStageSpatialProfiles
import Probes.ActualOriginalNormalPointPreparation
import Probes.ActualOriginalChartImmersion

/-! The actual stage map constructs its own unit free normal.  Its first and
Hessian profiles come from the original old pair budget, then the genuine
two-projection formula produces all new-normal derivatives.  The fixed
reference field and the reference-chart geometry are the only remaining
geometric inputs.  Constants are chosen before Data, SF, and its scale.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance normalFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance normalFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance normalFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance normalFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance

theorem round3_exists_uniform_actual_stage_free_normal_profiles
    (BS0 TS0 BP0 TP0 T Mv : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hT : ∀ j, 0 ≤ T j) (hMv : ∀ j, 0 ≤ Mv j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (r : ℕ)
    (budget cF cT mu : ℝ) (hbudget : 0 ≤ budget)
    (hcF : 0 < cF) (hcT : 0 < cT) (hmu : 0 < mu) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius r budget reference givenPacket)
    (j : ℕ) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (e : Ep → OpenPartialHomeomorph M D),
    (∀ p, e p ∈ maximalAtlas 𝓙 ∞ M) →
    let F := fun p x => Data.F ((Data.parameterChart i.2).symm p,x)
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference givenPacket stage)
      ((Data.parameterChart i.2).symm p)
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    ∀ (O Z : Set X) (v : X → Ey), IsOpen O → Z ⊆ O →
    ContDiffOn ℝ ∞ v O →
    ContDiffOn ℝ ∞ (round3OriginalAdaptedTransition Data.atlas i.1 e) O →
    (∀ z ∈ O, (e z.1).symm z.2 ∈ (Data.atlas.chart i.1).source) →
    (∀ z ∈ O, z.1 ∈ (Data.parameterChart i.2).target) →
    (∀ z ∈ O, z.2 ∈ (e z.1).target) →
    (∀ z ∈ Z, parameterTensorModelEquiv (m+1) d
      (round3OriginalAdaptedTransition Data.atlas i.1 e z) ∈ S i) →
    (∀ l, 1 ≤ l → l ≤ j+2 → ∀ z ∈ Z,
      ‖iteratedFDeriv ℝ l (round3OriginalAdaptedTransition Data.atlas i.1 e) z‖ ≤ T l) →
    (∀ k ≤ j, ∀ z ∈ Z, stage.ell^k*‖iteratedFDeriv ℝ k v z‖ ≤ Mv j) →
    (∀ z ∈ O, ∀ w : D, cF*‖w‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 w‖^2) →
    (∀ z ∈ O, ∀ w : Tdata, cT*‖w‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 w‖^2) →
    (∀ z ∈ O, mu ≤ ‖actualOriginalFreeNormalFieldRaw F hF e v z‖) →
    (∀ z ∈ O, Function.Injective (mfderiv 𝓙 𝓘(ℝ,Ey) (F z.1) ((e z.1).symm z.2))) ∧
    ContDiffOn ℝ ∞ (actualOriginalUnitFreeNormalField F hF e v) O ∧
    (∀ z ∈ O, ∃ normal : normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2),
      (normal : Ey) = actualOriginalUnitFreeNormalField F hF e v z ∧ ‖normal‖ = 1 ∧
      incrementsTransversePairing (F z.1) (hF z.1) ((e z.1).symm z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (e z.1).symm z.2 a.succ) normal = 0) ∧
    ∀ k ≤ j, ∀ z ∈ Z, stage.ell^k*‖iteratedFDeriv ℝ k
      (actualOriginalUnitFreeNormalField F hF e v) z‖ ≤ C j := by
  obtain ⟨Csp,hCsp,hSpatial⟩ := round3_exists_uniform_actual_stage_first_hessian_profiles
    (n := m+1) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 T hBS0 hTS0 hBP0 hTP0 hT Ds Dp radius hradius r
  have hNormal (j : ℕ) := actual_original_unit_free_normal_field_slow_jets
    (m := m) (N := N) («Ep» := Ep) (M := M) j cF cT (Csp j*budget) (Csp j*budget) mu (Mv j)
    hcF hcT (mul_nonneg (hCsp j) hbudget) (mul_nonneg (hCsp j) hbudget) hmu (hMv j)
  let C : ℕ → ℝ := fun j => Classical.choose (hNormal j)
  refine ⟨C,fun j => (Classical.choose_spec (hNormal j)).1,?_⟩
  intro Data reference givenPacket stage j i e he F hF S O Z v hO hZO hv hTransition hSource
    hParameter hcoord hSample hChartJets hvJets hFirst hFrame hReserve
  have hsp := hSpatial Data budget reference givenPacket stage j i e O Z hO hZO
    hTransition hSource hParameter hSample hChartJets
  have hSF := round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
    hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference givenPacket stage
  have hcoords : ∀ a, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F a)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart a) := by
    rw [← stage.chart_eq]
    exact parameterRound2_originalMapCoordinates_contDiffOn Data.atlas stage.parameterFamily.chart
      stage.atlas_smooth stage.parameter_smooth Data.F hSF
  have hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O :=
    round3_original_actual_adapted_contDiffOn Data.atlas Data.parameterChart Data.F hcoords i e O
      hTransition hSource hParameter
  have hImm (z : X) (hz : z ∈ O) : Function.Injective
      (mfderiv 𝓙 𝓘(ℝ,Ey) (F z.1) ((e z.1).symm z.2)) :=
    actual_increment_immersion_of_chart_reserve (F z.1) (hF z.1) (e z.1) (he z.1)
      z.2 (hcoord z hz) cF hcF (hFirst z hz)
  obtain ⟨hSmooth,hLegal,hBound⟩ := (Classical.choose_spec (hNormal j)).2
    F hF e he O Z hO hZO hcoord hJoint hImm stage.ell stage.ell_pos
    (fun z hz => hFirst z (hZO hz)) hFrame hsp.1.2 hsp.2.2 v hv hvJets
    (fun z hz => hReserve z (hZO hz))
  have hn (z : X) (hz : z ∈ O) : actualOriginalFreeNormalFieldRaw F hF e v z ≠ 0 :=
    norm_pos_iff.mp (hmu.trans_le (hReserve z hz))
  exact ⟨hImm,hSmooth.mono (fun z hz => ⟨hz,hn z hz⟩),
    fun z hz => actual_original_unit_free_normal_field_beta_at F hF e he v z (hcoord z hz) (hn z hz),
    hBound⟩

#print axioms round3_exists_uniform_actual_stage_free_normal_profiles
end GlobalEmbedding.Continuation
