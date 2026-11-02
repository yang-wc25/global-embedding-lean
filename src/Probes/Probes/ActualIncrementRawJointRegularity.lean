import Probes.ActualSecondaryOriginalRawFamilyAllIndex
import Probes.ActualSecondaryRawMetricData

/-! The SAME finite differential displacement is jointly smooth on the whole
valid open set, not merely at observation samples. The actual primary binding
and actual secondary piece regularity supply every smoothness conclusion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M Tr Label SubPrimary SubSecondary : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

omit [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype SubPrimary] in
theorem actual_constructed_secondary_joint_contMDiffOn
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    (data : ActualSecondarySignedRecord Label → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (tau : ℝ) (length : ℕ) (hW : IsOpen W) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞
      (actualConstructedSecondarySum F hF (fun r a => (data r a).base) tau length) W := by
  change ContMDiffOn _ _ ∞ (fun z => actualSecondaryRefinedNonzeroSum
    (actualConstructedSecondaryFamily F hF (fun r a => (data r a).base) tau length) z) W
  rw [actual_secondary_refined_sum_eq_records]
  apply contMDiffOn_finsetSum
  intro r hr
  apply contMDiffOn_finsetSum
  intro a _
  have hq := (Finset.mem_filter.mp hr).2
  simpa only [actualConstructedSecondaryFamily,dif_pos hq] using
    ((data ⟨r,hq⟩ a).base.wave_regular tau length hW).1

theorem actual_original_increment_raw_joint_contMDiffOn
    (nInput nSolve j q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hc : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (W : Set (Ep × M)) (primary : Label → Set (Ep × M)) (ell delta tau Delta : ℝ)
    (htau : 0 < tau)
    (prim : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
    (raw : ActualOriginalSecondaryRawData (Tr := Tr) F hF g input inputbar nInput nSolve j q Rsub Lprimary
      reserve Bnd Mg Kcut T Tinv W primary ell delta tau Delta choice) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞
      (actualOriginalIncrementMap F hF g input (q+2) tau delta choice) W := by
  obtain ⟨CH,hCH,hFamily⟩ := actual_original_secondary_family_from_raw_uniform_all_index
    (m := m) (N := N) (Ep := Ep) (M := M) (Tr := Tr)
    nInput nSolve q Rsub Lprimary hq hInput reserve Bnd Mg Kcut hc hBnd hMg hKcut T Tinv hT hTinv
  obtain ⟨data,_,hsum⟩ := hFamily Label SubPrimary SubSecondary F hF g input inputbar W primary
    (j+1) ell delta tau Delta choice raw.geometry raw.coordinate raw.chart raw.phase raw.host raw.hostInverse
    raw.hostSource raw.cutoffSupport raw.cutoffSmooth raw.inverseSmooth raw.hostProfiles raw.cutoffJets raw.inverseJets
  have hsecond := actual_constructed_secondary_joint_contMDiffOn F hF data tau (q+2) prim.hW
  rw [hsum] at hsecond
  have hfirst := increments_global_primary_mean_binding F hF g input q hq tau htau
    W prim.hW primary prim.hPrimary prim.hPrimarySupport prim.hSourceW prim.hChart prim.hChartInv prim.hInverse
    prim.hCombinedSupport prim.hPhase prim.hCut prim.hNormal prim.hArgument prim.hEta prim.hPositive prim.hUnit
    prim.hPartition prim.hSymm prim.hDecomp prim.hDouble prim.hInteraction prim.hG prim.hJ prim.hT0 prim.hA prim.hB prim.hSecond
  have hscaled : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞
      (fun y => delta • incrementsGlobalPrimaryWave F hF g input (q+2) tau y) W := by
    exact (delta • ContinuousLinearMap.id ℝ V).contDiff.contMDiff.comp_contMDiffOn hfirst.1
  exact hscaled.add hsecond

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_constructed_secondary_joint_contMDiffOn
#print axioms GlobalEmbedding.Continuation.actual_original_increment_raw_joint_contMDiffOn
