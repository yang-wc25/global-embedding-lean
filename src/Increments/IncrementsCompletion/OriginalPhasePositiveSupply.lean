import IncrementsBridge.OriginalPhaseChartFiniteBudget
import Probes.ActualOriginalHostRefinement
import Probes.Round3ParameterChartPullback

/-!
# Actual original phase charts and positive sampled profiles

Only the original low-order Given bounds choose the chart.  The same
constructed chart is lifted to the original manifold host and sliced by
the existing actual chart theorem.  Every subsequent positive jet is
estimated on the unchanged original samples by an explicit numerical
profile.  No chart, inverse, slice, or output profile is supplied as an
entrance assumption.

The noncritical margin here is the literal positive norm of the original
spatial phase differential at the chosen point.  This local producer does
not assert a uniform lower margin over an entire refinement, manufacture a
covering partition, or solve the remaining global finite-budget entrance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal
namespace GlobalEmbedding.Continuation

theorem incrementsCompletion_original_phase_jet_cost_nonneg (m d j : ℕ) :
    0 ≤ actualOriginalTotalPhaseJetCost (m+1) d j := by
  unfold actualOriginalTotalPhaseJetCost
  exact mul_nonneg (mul_nonneg (linearModelFactor_nonneg _ _)
    (ContinuousLinearMap.opNorm_nonneg (actualScalarCovectorAssembly (m+1+d))))
    (coordinateDimensionFactor_nonneg _ _)

def incrementsCompletionOriginalPhaseForwardProfile (m d : ℕ) (Packet : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else if j = 1 then 2*(1+2*incrementsBridgeOriginalPhaseLowBudget m d Packet)
  else 2^(j+1)*actualOriginalTotalPhaseJetCost (m+1) d (j-1)*max 0 (Packet (j-1))

def incrementsCompletionOriginalPhaseInverseProfile
    (m d : ℕ) (mu : ℝ) (Packet : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else
    actualEuclideanPhaseSampleInverseJetCost mu (incrementsBridgeOriginalPhaseLowBudget m d Packet)
      (actualOriginalTotalPhaseJetCost (m+1) d (j-1)*max 0 (Packet (j-1))) (j-1)

theorem incrementsCompletionOriginalPhaseForwardProfile_nonneg
    (m d : ℕ) (Packet : ℕ → ℝ) (j : ℕ) :
    0 ≤ incrementsCompletionOriginalPhaseForwardProfile m d Packet j := by
  unfold incrementsCompletionOriginalPhaseForwardProfile
  split_ifs
  · exact le_rfl
  · unfold incrementsBridgeOriginalPhaseLowBudget
    positivity
  · exact mul_nonneg (mul_nonneg (by positivity)
      (incrementsCompletion_original_phase_jet_cost_nonneg m d (j-1))) (le_max_left _ _)

theorem incrementsCompletionOriginalPhaseInverseProfile_nonneg
    (m d : ℕ) (mu : ℝ) (hmu : 0 < mu) (Packet : ℕ → ℝ) (j : ℕ) :
    0 ≤ incrementsCompletionOriginalPhaseInverseProfile m d mu Packet j := by
  unfold incrementsCompletionOriginalPhaseInverseProfile
  split_ifs
  · exact le_rfl
  · apply actualEuclideanPhaseSampleInverseJetCost_nonneg hmu
    · unfold incrementsBridgeOriginalPhaseLowBudget
      positivity
    · exact mul_nonneg (incrementsCompletion_original_phase_jet_cost_nonneg m d (j-1))
        (le_max_left _ _)

/-- Only the low chart-selection slots and the indicated positive jet slot
are read; all higher original profile values are irrelevant to this cost. -/
theorem incrementsCompletionOriginalPhaseProfiles_prefix_congr
    (m d : ℕ) (mu : ℝ) (Packet Packet' : ℕ → ℝ) (j : ℕ)
    (h : ∀ k, k ≤ max 1 (j-1) → Packet k = Packet' k) :
    incrementsCompletionOriginalPhaseForwardProfile m d Packet j =
      incrementsCompletionOriginalPhaseForwardProfile m d Packet' j ∧
    incrementsCompletionOriginalPhaseInverseProfile m d mu Packet j =
      incrementsCompletionOriginalPhaseInverseProfile m d mu Packet' j := by
  have hLow := incrementsBridge_original_phase_low_budget_prefix m d Packet Packet'
    (fun k hk => h k (hk.trans (le_max_left _ _)))
  simp only [incrementsCompletionOriginalPhaseForwardProfile,
    incrementsCompletionOriginalPhaseInverseProfile,hLow,h (j-1) (le_max_right _ _)]
  exact ⟨trivial,trivial⟩

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

theorem incrementsCompletion_original_phase_positive_supply
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (ell : ℝ) (hell : 0 < ell) (Packet : ℕ → ℝ)
    (hFinite : ∀ j, j ≤ 1 → actualOriginalGivenInputProfile Data j ell ≠ ⊤)
    (hBudget : ∀ j, j ≤ 1 → (actualOriginalGivenInputProfile Data j ell).toReal ≤ Packet j)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (z0 : X)
    (hz0 : parameterTensorModelEquiv (m+1) d z0 ∈ incrementsOriginalPrimaryEvaluation Data nu i) :
    let psi := actualOriginalJointPhase Data nu i ∘ parameterTensorModelEquiv (m+1) d
    let mu := ‖(fderiv ℝ psi z0).comp (ContinuousLinearMap.inr ℝ Ep D)‖
    0 < mu ∧ ∃ (native : OpenPartialHomeomorph X X)
      (slices : Ep → OpenPartialHomeomorph M D),
      z0 ∈ native.source ∧ native.source ⊆ actualOriginalPrimaryNativeOpen Data nu i ∧
      ActualOriginalHostSliceData (Data.atlas.chart i.1) native
        (fun w : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm w.1,w.2)) slices ∧
      Round3ParameterChartPreserves native ∧
      ∀ j, 1 ≤ j →
        actualOriginalGivenInputProfile Data (j-1) ell ≠ ⊤ →
        (actualOriginalGivenInputProfile Data (j-1) ell).toReal ≤ Packet (j-1) →
      ∀ z ∈ native.source, parameterTensorModelEquiv (m+1) d z ∈
          incrementsOriginalPrimaryEvaluation Data nu i →
        ell^(j-1)*‖iteratedFDeriv ℝ j native z‖ ≤
          incrementsCompletionOriginalPhaseForwardProfile m d Packet j ∧
        ell^(j-1)*‖iteratedFDeriv ℝ j native.symm (native z)‖ ≤
          incrementsCompletionOriginalPhaseInverseProfile m d mu Packet j := by
  intro psi mu
  obtain ⟨hmu,native,hzNative,hNativeOpen,hn,hni,hparam,hback,hfirst,higher,hinverse⟩ :=
    incrementsBridge_original_phase_actual_chart_all_orders Data hd hs hp ell hell Packet
      hFinite hBudget nu i z0 hz0
  have hpsi : psi = fun z : X => Data.phase nu
      ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) := by
    funext z
    simp only [psi,Function.comp_apply,actualOriginalJointPhase,actual_original_jointPoint_native]
  have hSource : native.source ⊆
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).target := by
    intro z hz
    have hOpen := round3_prepared_primary_native_subset Data i nu (hNativeOpen hz)
    exact ⟨mem_univ _,actualOriginalNativeMap_source_target Data i hOpen.1⟩
  obtain ⟨hat,ha,hai,hforw,slices,hSlices⟩ := actual_adapted_chart_original_host
    (Data.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1)
    (fun w : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm w.1,w.2)) native
    hSource hn hni (fun z hz => (hparam z hz).1) (fun z hz =>
      (hparam z hz).2.trans (congrFun hpsi z))
  have hData : ActualOriginalHostSliceData (Data.atlas.chart i.1) native
      (fun w : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm w.1,w.2)) slices :=
    ⟨hat,ha,hai,hforw,hSlices⟩
  refine ⟨hmu,native,slices,hzNative,hNativeOpen,hData,fun z hz => (hparam z hz).1,?_⟩
  intro j hj hFin hBud z hz hSample
  have hj0 : j ≠ 0 := by omega
  constructor
  · by_cases hj1 : j = 1
    · subst j
      simpa only [Nat.sub_self,pow_zero,one_mul,norm_iteratedFDeriv_one,
        incrementsCompletionOriginalPhaseForwardProfile,ite_false,ite_true,Nat.one_ne_zero] using hfirst z hz
    · have hHigh := higher (j-1) (by omega) z hz
      rw [Nat.sub_add_cancel hj] at hHigh
      have hPhase := actual_original_given_phase_positive_jets Data hd hs (j-1) ell
        (max 0 (Packet (j-1))) hell hFin (hBud.trans (le_max_right _ _))
        nu i (j-1) le_rfl z hSample
      rw [Nat.sub_add_cancel hj] at hPhase
      rw [incrementsCompletionOriginalPhaseForwardProfile,if_neg hj0,if_neg hj1]
      calc
        ell^(j-1)*‖iteratedFDeriv ℝ j native z‖ ≤
            ell^(j-1)*(2^((j-1)+2)*‖iteratedFDeriv ℝ j psi z‖) :=
          mul_le_mul_of_nonneg_left hHigh (pow_nonneg hell.le _)
        _ = 2^(j+1)*(ell^(j-1)*‖iteratedFDeriv ℝ j psi z‖) := by
          rw [show (j-1)+2 = j+1 by omega]
          ring
        _ ≤ 2^(j+1)*(actualOriginalTotalPhaseJetCost (m+1) d (j-1)*max 0 (Packet (j-1))) :=
          mul_le_mul_of_nonneg_left hPhase (by positivity)
        _ = _ := by ring
  · have hS : ({native z} : Set X) ⊆ native.target := by
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact native.map_source hz
    have hSamples : ∀ w ∈ native.symm '' ({native z} : Set X),
        parameterTensorModelEquiv (m+1) d w ∈ incrementsOriginalPrimaryEvaluation Data nu i := by
      rintro w ⟨y,hy,rfl⟩
      rcases Set.mem_singleton_iff.mp hy with rfl
      simpa only [native.left_inv hz] using hSample
    have hInv := hinverse {native z} hS hSamples (j-1) (max 0 (Packet (j-1))) hFin
      (hBud.trans (le_max_right _ _)) j hj (by omega) (native z) (Set.mem_singleton _)
    simpa only [incrementsCompletionOriginalPhaseInverseProfile,if_neg hj0] using hInv

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.incrementsCompletionOriginalPhaseProfiles_prefix_congr
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_phase_positive_supply
