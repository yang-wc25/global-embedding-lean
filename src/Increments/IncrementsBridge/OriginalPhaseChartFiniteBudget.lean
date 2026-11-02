import Probes.ActualPhaseEuclideanSampleChart
import Probes.Round3PreparedPrimaryPhase

/-!
# Actual original-phase charts with a finite low-order input budget

The chart below is constructed, not supplied. Its construction reads the
original phase, its nonzero spatial differential, and the original first two
derivative bounds. A possibly smaller neighbourhood is used only to preserve
the original open domain; its radius is absent from the inverse-jet constants.
The one resulting chart supplies every later observation order on the literal
original samples. In particular no phase-value bound is introduced.

This closes the local inverse-chart part of the original increments budget
bridge. It does not claim that the derivative costs of a subordinate partition
or the original given-family overlap budget have been discharged.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

section Local
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep]
  {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

/-- A chart made from low-order bounds at the actual input point. Continuity
chooses its domain inside the prescribed open set, while the same explicit
inverse-jet budget works on every subsequent sample and at every order. -/
theorem incrementsBridge_phase_chart_from_point_bounds
    (psi : X → ℝ) (U : Set X) (hU : IsOpen U)
    (hpsi : ContDiffOn ℝ ∞ psi U) (z0 : X) (hz0 : z0 ∈ U)
    (ell mu B : ℝ) (hell : 0 < ell) (hmu : 0 < mu) (hB : 0 ≤ B)
    (hspatial : mu ≤ ‖(fderiv ℝ psi z0).comp (ContinuousLinearMap.inr ℝ Ep D)‖)
    (hfirst : ‖fderiv ℝ psi z0‖ < B)
    (hsecond : ell*‖iteratedFDeriv ℝ 2 psi z0‖ < B) :
    ∃ a : OpenPartialHomeomorph X X,
      z0 ∈ a.source ∧ a.source ⊆ U ∧
      ContDiffOn ℝ ∞ a a.source ∧ ContDiffOn ℝ ∞ a.symm a.target ∧
      (∀ z ∈ a.source, (a z).1 = z.1 ∧ (a z).2 0 = psi z) ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧ psi (a.symm z) = z.2 0) ∧
      (∀ z ∈ a.source, ‖fderiv ℝ a z‖ ≤ 2*(1+2*B)) ∧
      (∀ k, 1 ≤ k → ∀ z ∈ a.source,
        ‖iteratedFDeriv ℝ (k+1) a z‖ ≤ 2^(k+2)*‖iteratedFDeriv ℝ (k+1) psi z‖) ∧
      ∀ (S : Set X), S ⊆ a.target → ∀ (j : ℕ) (weight Mj : ℝ),
        0 < weight → 0 ≤ Mj →
        (∀ k, 1 ≤ k → k ≤ j → ∀ z ∈ a.symm '' S,
          weight^k*‖iteratedFDeriv ℝ (k+1) psi z‖ ≤ Mj) →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ z ∈ S,
          weight^(k-1)*‖iteratedFDeriv ℝ k a.symm z‖ ≤
            actualEuclideanPhaseSampleInverseJetCost mu B Mj j := by
  have hfirstCont : ContinuousAt (fun z => ‖fderiv ℝ psi z‖) z0 :=
    (hpsi.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt
      (hU.mem_nhds hz0) |>.norm
  have hsecondCont : ContinuousOn (iteratedFDeriv ℝ 2 psi) U := by
    apply (hpsi.continuousOn_iteratedFDerivWithin (m := 2) (by simp) hU.uniqueDiffOn).congr
    intro z hz
    exact (iteratedFDerivWithin_of_isOpen _ hU hz).symm
  have hsecondAt : ContinuousAt (fun z => ell*‖iteratedFDeriv ℝ 2 psi z‖) z0 :=
    continuousAt_const.mul ((hsecondCont.continuousAt (hU.mem_nhds hz0)).norm)
  have hnear : U ∩ {z | ‖fderiv ℝ psi z‖ < B ∧ ell*‖iteratedFDeriv ℝ 2 psi z‖ < B} ∈ 𝓝 z0 :=
    inter_mem (hU.mem_nhds hz0)
      ((hfirstCont.eventually_lt_const hfirst).and (hsecondAt.eventually_lt_const hsecond))
  obtain ⟨r0,hr0,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let r := min r0 ell
  have hr : 0 < r := lt_min hr0 hell
  have hr0le : r ≤ r0 := min_le_left _ _
  have hrell : r ≤ ell := min_le_right _ _
  have hball' : ball z0 r ⊆ U ∩
      {z | ‖fderiv ℝ psi z‖ < B ∧ ell*‖iteratedFDeriv ℝ 2 psi z‖ < B} :=
    (ball_subset_ball hr0le).trans hball
  obtain ⟨a,hi,ho,ha,hai,hp,hpi,_ht,hf,higher,hinverse⟩ :=
    actual_exists_native_euclidean_quantitative_phase_chart_sample_jets mu B hmu hB
      psi z0 r hr (hpsi.mono (fun z hz => (hball' hz).1)) hspatial
      (fun z hz => (hball' hz).2.1.le) (fun z hz =>
        (mul_le_mul_of_nonneg_right hrell (norm_nonneg _)).trans (hball' hz).2.2.le)
  have hinvpos : 0 < actualPhaseInverseConstant mu (2*B) :=
    zero_lt_one.trans_le (actualPhaseInverseConstant_one_le hmu (by positivity))
  have hrad : 0 < actualEuclideanPhaseRadius mu B r := by
    unfold actualEuclideanPhaseRadius
    positivity
  exact ⟨a,hi (mem_ball_self hrad),ho.trans (fun z hz => (hball' hz).1),
    ha,hai,hp,hpi,hf,higher,hinverse⟩

end Local

section Original
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

/-- A numerical bound reading only orders zero and one of the ORIGINAL
phase-differential input profile. No generated-chart value is an input. -/
def incrementsBridgeOriginalPhaseLowBudget (m d : ℕ) (Packet : ℕ → ℝ) : ℝ :=
  1 + |actualOriginalTotalPhaseJetCost (m+1) d 0*Packet 0| +
    |actualOriginalTotalPhaseJetCost (m+1) d 1*Packet 1|

theorem incrementsBridge_original_phase_low_budget_prefix
    (m d : ℕ) (Packet Packet' : ℕ → ℝ)
    (h : ∀ k, k ≤ 1 → Packet k = Packet' k) :
    incrementsBridgeOriginalPhaseLowBudget m d Packet =
      incrementsBridgeOriginalPhaseLowBudget m d Packet' := by
  unfold incrementsBridgeOriginalPhaseLowBudget
  rw [h 0 (by omega),h 1 le_rfl]

/-- The actual given phase supplies both the adapted chart and its entire
sampled inverse-jet family. Higher input orders change only the estimate at
that order, never the selected chart. The original phase, chart pullback,
norm samples and finite parameter variables are unchanged. -/
theorem incrementsBridge_original_phase_actual_chart_all_orders
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (ell : ℝ) (hell : 0 < ell)
    (Packet : ℕ → ℝ)
    (hFinite : ∀ j, j ≤ 1 → actualOriginalGivenInputProfile Data j ell ≠ ⊤)
    (hBudget : ∀ j, j ≤ 1 → (actualOriginalGivenInputProfile Data j ell).toReal ≤ Packet j)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (z0 : X)
    (hz0 : parameterTensorModelEquiv (m+1) d z0 ∈ incrementsOriginalPrimaryEvaluation Data nu i) :
    let psi := actualOriginalJointPhase Data nu i ∘ parameterTensorModelEquiv (m+1) d
    let mu := ‖(fderiv ℝ psi z0).comp (ContinuousLinearMap.inr ℝ Ep D)‖
    let B := incrementsBridgeOriginalPhaseLowBudget m d Packet
    0 < mu ∧ ∃ a : OpenPartialHomeomorph X X,
      z0 ∈ a.source ∧ a.source ⊆ actualOriginalPrimaryNativeOpen Data nu i ∧
      ContDiffOn ℝ ∞ a a.source ∧ ContDiffOn ℝ ∞ a.symm a.target ∧
      (∀ z ∈ a.source, (a z).1 = z.1 ∧ (a z).2 0 = psi z) ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧ psi (a.symm z) = z.2 0) ∧
      (∀ z ∈ a.source, ‖fderiv ℝ a z‖ ≤ 2*(1+2*B)) ∧
      (∀ k, 1 ≤ k → ∀ z ∈ a.source,
        ‖iteratedFDeriv ℝ (k+1) a z‖ ≤ 2^(k+2)*‖iteratedFDeriv ℝ (k+1) psi z‖) ∧
      ∀ (S : Set X), S ⊆ a.target →
        (∀ z ∈ a.symm '' S, parameterTensorModelEquiv (m+1) d z ∈
          incrementsOriginalPrimaryEvaluation Data nu i) →
        ∀ j budget,
          actualOriginalGivenInputProfile Data j ell ≠ ⊤ →
          (actualOriginalGivenInputProfile Data j ell).toReal ≤ budget →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ z ∈ S,
          ell^(k-1)*‖iteratedFDeriv ℝ k a.symm z‖ ≤
            actualEuclideanPhaseSampleInverseJetCost mu B
              (actualOriginalTotalPhaseJetCost (m+1) d j*budget) j := by
  intro psi mu B
  let U := actualOriginalPrimaryNativeOpen Data nu i
  have hU : IsOpen U := actualOriginalPrimaryNativeOpen_isOpen Data hd nu i
  have hpsiEq : psi = fun z : X => Data.phase nu
      ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) := by
    funext z
    simp only [psi,Function.comp_apply,actualOriginalJointPhase,actual_original_jointPoint_native]
  have hpsi : ContDiffOn ℝ ∞ psi U := by
    rw [hpsiEq]
    exact round3_actual_original_primary_native_phase_smooth Data hd hs nu i
  have hzU : z0 ∈ U := by
    refine ⟨⟨hz0.1.1,hz0.2⟩,?_⟩
    exact ⟨hd.parameter_subset hz0.1.2.2.2,mem_univ _⟩
  have hactive := round3_prepared_native_primary_active Data i nu hzU
  have hgood := hp.primary_good nu _ hactive
  have hTarget : z0.2 ∈ (Data.atlas.chart i.1).target :=
    actualOriginalNativeMap_source_target Data i hz0.1.1
  have hmu : 0 < mu := by
    apply norm_pos_iff.mpr
    rw [hpsiEq]
    have hdiff : DifferentiableAt ℝ psi z0 :=
      (hpsi.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
    rw [hpsiEq] at hdiff
    exact round3_actual_host_phase_spatial_ne_zero (Data.atlas.chart i.1)
      (hd.atlas_smooth.chart_mem i.1)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2))
      z0 hTarget hdiff hgood.1
  have hInput (j k : ℕ) (budget : ℝ)
      (hFin : actualOriginalGivenInputProfile Data j ell ≠ ⊤)
      (hBud : (actualOriginalGivenInputProfile Data j ell).toReal ≤ budget)
      (hk : k ≤ j) (z : X)
      (hz : parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalPrimaryEvaluation Data nu i) :
      ell^k*‖iteratedFDeriv ℝ (k+1) psi z‖ ≤
        actualOriginalTotalPhaseJetCost (m+1) d j*budget :=
    actual_original_given_phase_positive_jets Data hd hs j ell budget hell
      hFin hBud nu i k hk z hz
  have hfirstBound : ‖fderiv ℝ psi z0‖ ≤ actualOriginalTotalPhaseJetCost (m+1) d 0*Packet 0 := by
    have h := hInput 0 0 (Packet 0) (hFinite 0 (by omega)) (hBudget 0 (by omega)) le_rfl z0 hz0
    change 1*‖iteratedFDeriv ℝ 1 psi z0‖ ≤ _ at h
    simpa only [one_mul,norm_iteratedFDeriv_one] using h
  have hsecondBound : ell*‖iteratedFDeriv ℝ 2 psi z0‖ ≤ actualOriginalTotalPhaseJetCost (m+1) d 1*Packet 1 := by
    simpa only [pow_one] using hInput 1 1 (Packet 1) (hFinite 1 le_rfl) (hBudget 1 le_rfl) le_rfl z0 hz0
  have hB : 0 < B := by dsimp [B,incrementsBridgeOriginalPhaseLowBudget]; positivity
  have hfirst : ‖fderiv ℝ psi z0‖ < B := by
    have h0 := hfirstBound.trans (le_abs_self _)
    have h1 := abs_nonneg (actualOriginalTotalPhaseJetCost (m+1) d 1*Packet 1)
    dsimp [B,incrementsBridgeOriginalPhaseLowBudget]
    linarith
  have hsecond : ell*‖iteratedFDeriv ℝ 2 psi z0‖ < B := by
    have h1 := hsecondBound.trans (le_abs_self _)
    have h0 := abs_nonneg (actualOriginalTotalPhaseJetCost (m+1) d 0*Packet 0)
    dsimp [B,incrementsBridgeOriginalPhaseLowBudget]
    linarith
  obtain ⟨a,hzA,hAU,ha,hai,hpA,hpi,hfirstA,higherA,hInverse⟩ :=
    incrementsBridge_phase_chart_from_point_bounds psi U hU hpsi z0 hzU ell mu B
      hell hmu hB.le le_rfl hfirst hsecond
  refine ⟨hmu,a,hzA,hAU,ha,hai,hpA,hpi,hfirstA,higherA,?_⟩
  intro S hS hSamples j budget hFin hBud k hk hkj z hz
  have hCost : 0 ≤ actualOriginalTotalPhaseJetCost (m+1) d j*budget := by
    have hModel := linearModelFactor_nonneg (parameterTensorModelEquiv (m+1) d) (j+1)
    have hDim := coordinateDimensionFactor_nonneg (m+1+d) j
    have hBudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hBud
    unfold actualOriginalTotalPhaseJetCost
    positivity
  exact hInverse S hS j ell (actualOriginalTotalPhaseJetCost (m+1) d j*budget)
    hell hCost (fun r _hr hrj y hy => hInput j r budget hFin hBud hrj y (hSamples y hy)) k hk hkj z hz

end Original
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.incrementsBridge_phase_chart_from_point_bounds
#print axioms GlobalEmbedding.Continuation.incrementsBridge_original_phase_low_budget_prefix
#print axioms GlobalEmbedding.Continuation.incrementsBridge_original_phase_actual_chart_all_orders
