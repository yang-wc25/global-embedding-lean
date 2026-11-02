import Probes.ActualSecondaryMetricPairing

/-!
# Joint jets of the actual secondary metric cross/self terms

The same native bilinear metric tensor is used throughout. The expression
contains both cross terms and the quadratic self term of the secondary
spatial derivative. These are actual function jets, not scalar stand-ins.
-/

noncomputable section
open Set Filter GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {X D V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private noncomputable local instance metricJetsTensorSemi :
    SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance metricJetsTensorNormed :
    NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance metricJetsTensorSpace :
    NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance metricJetsPartialSemi :
    SeminormedAddCommGroup ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance metricJetsPartialNormed :
    NormedAddCommGroup ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance metricJetsPartialSpace :
    NormedSpace ℝ ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Weighted joint jets of the exact secondary cross/self metric expression. -/
theorem actual_metric_cross_self_weighted_jets
    (A B : X → D →L[ℝ] V) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (j : ℕ) (scale KA KB : ℝ) (hscale : 0 ≤ scale) (hKA : 0 ≤ KA) (hKB : 0 ≤ KB)
    (hAb : ∀ r ≤ j, ∀ z ∈ S, scale ^ r * ‖iteratedFDeriv ℝ r A z‖ ≤ KA)
    (hBb : ∀ r ≤ j, ∀ z ∈ S, scale ^ r * ‖iteratedFDeriv ℝ r B z‖ ≤ KB) :
    let R := fun z => actualMetricJetPairing (A z) (B z) +
      actualMetricJetPairing (B z) (A z) + actualSpatialMetric (B z)
    ContDiffOn ℝ ∞ R O ∧
      ∀ r ≤ j, ∀ z ∈ S, scale ^ r * ‖iteratedFDeriv ℝ r R z‖ ≤
        2 ^ j * (2 * KA * KB + KB ^ 2) := by
  intro R
  let P : (D →L[ℝ] V) →L[ℝ] (D →L[ℝ] V) →L[ℝ] (D →L[ℝ] D →L[ℝ] ℝ) :=
    actualMetricJetPairing (D := D) (V := V)
  have hab : ContDiffOn ℝ ∞ (fun z => P (A z) (B z)) O :=
    (P.contDiff.comp_contDiffOn hA).clm_apply hB
  have hba : ContDiffOn ℝ ∞ (fun z => P (B z) (A z)) O :=
    (P.contDiff.comp_contDiffOn hB).clm_apply hA
  have hbb : ContDiffOn ℝ ∞ (fun z => P (B z) (B z)) O :=
    (P.contDiff.comp_contDiffOn hB).clm_apply hB
  refine ⟨(hab.add hba).add hbb, ?_⟩
  intro r hr z hz
  have hp : ‖P‖ ≤ 1 := actualMetricJetPairing_norm_le
  have habb := slow_bilinear_jet_bound_norm P O hO A B hA hB r scale KA KB hscale z (hSO hz)
    (fun k hk => hAb k (hk.trans hr) z hz) (fun k hk => hBb k (hk.trans hr) z hz)
  have hbab := slow_bilinear_jet_bound_norm P O hO B A hB hA r scale KB KA hscale z (hSO hz)
    (fun k hk => hBb k (hk.trans hr) z hz) (fun k hk => hAb k (hk.trans hr) z hz)
  have hbbb := slow_bilinear_jet_bound_norm P O hO B B hB hB r scale KB KB hscale z (hSO hz)
    (fun k hk => hBb k (hk.trans hr) z hz) (fun k hk => hBb k (hk.trans hr) z hz)
  have hfac : (2 : ℝ) ^ r ≤ 2 ^ j := by gcongr <;> norm_num
  have habb' : scale ^ r * ‖iteratedFDeriv ℝ r (fun w => P (A w) (B w)) z‖ ≤
      2 ^ j * KA * KB := habb.trans (by gcongr; exact mul_le_of_le_one_left hKA hp)
  have hbab' : scale ^ r * ‖iteratedFDeriv ℝ r (fun w => P (B w) (A w)) z‖ ≤
      2 ^ j * KB * KA := hbab.trans (by gcongr; exact mul_le_of_le_one_left hKB hp)
  have hbbb' : scale ^ r * ‖iteratedFDeriv ℝ r (fun w => P (B w) (B w)) z‖ ≤
      2 ^ j * KB * KB := hbbb.trans (by gcongr; exact mul_le_of_le_one_left hKB hp)
  have hdab := (hab.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp : (r : ℕ∞ω) ≤ ∞)
  have hdba := (hba.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp : (r : ℕ∞ω) ≤ ∞)
  have hdbb := (hbb.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp : (r : ℕ∞ω) ≤ ∞)
  change scale ^ r * ‖iteratedFDeriv ℝ r
    (fun w => P (A w) (B w) + P (B w) (A w) + P (B w) (B w)) z‖ ≤ _
  rw [fun_iteratedFDeriv_add_apply (hdab.add hdba) hdbb,
    fun_iteratedFDeriv_add_apply hdab hdba]
  calc
    _ ≤ scale ^ r * (‖iteratedFDeriv ℝ r (fun w => P (A w) (B w)) z‖ +
        ‖iteratedFDeriv ℝ r (fun w => P (B w) (A w)) z‖ +
        ‖iteratedFDeriv ℝ r (fun w => P (B w) (B w)) z‖) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)) (pow_nonneg hscale _)
    _ ≤ 2 ^ j * KA * KB + 2 ^ j * KB * KA + 2 ^ j * KB * KB := by
      nlinarith [habb', hbab', hbbb']
    _ = _ := by ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_metric_cross_self_weighted_jets
