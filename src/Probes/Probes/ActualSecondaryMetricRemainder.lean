import Probes.ActualSecondaryMetricJets

/-!
# The actual δ³/τ secondary metric remainder

For the SAME primary and secondary displacement functions, the exact
quadratic metric difference contains their two cross terms and the secondary
self term. All parameter and spatial derivatives remain inside native joint
iterated derivatives. One genuine spatial derivative is charged to each
displacement. The secondary self term is absorbed using only `0 ≤ δ ≤ τ`.
-/

noncomputable section
open Set Filter GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep D V : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private noncomputable local instance metricRemTensorSemi :
    SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance metricRemTensorNormed :
    NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance metricRemTensorSpace :
    NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance metricRemPartialSemi :
    SeminormedAddCommGroup ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance metricRemPartialNormed :
    NormedAddCommGroup ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- A true spatial derivative consumes exactly one fast scale, including
all mixed parameter derivatives of that derivative field. -/
theorem actual_fast_spatial_first_weighted_jets
    (U : Ep × D → V) (O S : Set (Ep × D)) (hO : IsOpen O) (hSO : S ⊆ O)
    (hU : ContDiffOn ℝ ∞ U O) (j : ℕ) (tau K : ℝ) (htau : 0 < tau)
    (hUb : ∀ r ≤ j + 1, ∀ z ∈ S, tau ^ r * ‖iteratedFDeriv ℝ r U z‖ ≤ K) :
    ∀ r ≤ j, ∀ z ∈ S, tau ^ r * ‖iteratedFDeriv ℝ r
      (fun w : Ep × D => fderiv ℝ (fun x => U (w.1, x)) w.2) z‖ ≤ K / tau := by
  intro r hr z hz
  apply (mul_le_mul_of_nonneg_left (spatial_first_jet_le hO hU (hSO hz) r)
    (pow_nonneg htau.le r)).trans
  apply (le_div_iff₀ htau).2
  simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
    hUb (r + 1) (by omega) z hz

/-- Exact native metric expansion on the actual open domain of the family. -/
theorem actual_spatial_metric_displacement_add
    (U W : Ep × D → V) (O : Set (Ep × D)) (hO : IsOpen O)
    (hU : ContDiffOn ℝ ∞ U O) (hW : ContDiffOn ℝ ∞ W O) :
    EqOn (fun z : Ep × D =>
      actualSpatialMetric (fderiv ℝ (fun x => U (z.1, x) + W (z.1, x)) z.2) -
        actualSpatialMetric (fderiv ℝ (fun x => U (z.1, x)) z.2))
      (fun z : Ep × D =>
        actualMetricJetPairing (fderiv ℝ (fun x => U (z.1, x)) z.2)
          (fderiv ℝ (fun x => W (z.1, x)) z.2) +
        actualMetricJetPairing (fderiv ℝ (fun x => W (z.1, x)) z.2)
          (fderiv ℝ (fun x => U (z.1, x)) z.2) +
        actualSpatialMetric (fderiv ℝ (fun x => W (z.1, x)) z.2)) O := by
  intro z hz
  dsimp only
  have hu := (hU.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hw := (hW.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hsum := (incrementsJointSpatialJets_bridge (fun z => U z + W z) O hO (hU.add hW)).1 z hz
  have hu' := (incrementsJointSpatialJets_bridge U O hO hU).1 z hz
  have hw' := (incrementsJointSpatialJets_bridge W O hO hW).1 z hz
  rw [hsum, fderiv_fun_add hu hw, ContinuousLinearMap.add_comp, ← hu', ← hw']
  exact actualSpatialMetric_add_sub _ _

/-- The primary/secondary metric remainder has the ORIGINAL δ³/τ scale.
The hypotheses are jets of the actual two maps, and the conclusion is the
metric of their literal sum minus the metric of the same primary map. -/
theorem actual_secondary_metric_remainder_weighted_jets
    (U W : Ep × D → V) (O S : Set (Ep × D)) (hO : IsOpen O) (hSO : S ⊆ O)
    (hU : ContDiffOn ℝ ∞ U O) (hW : ContDiffOn ℝ ∞ W O)
    (j : ℕ) (tau delta M1 M2 : ℝ) (htau : 0 < tau)
    (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hUb : ∀ r ≤ j + 1, ∀ z ∈ S, tau ^ r * ‖iteratedFDeriv ℝ r U z‖ ≤ M1 * delta * tau)
    (hWb : ∀ r ≤ j + 1, ∀ z ∈ S, tau ^ r * ‖iteratedFDeriv ℝ r W z‖ ≤ M2 * delta ^ 2) :
    let R := fun z : Ep × D =>
      actualSpatialMetric (fderiv ℝ (fun x => U (z.1, x) + W (z.1, x)) z.2) -
        actualSpatialMetric (fderiv ℝ (fun x => U (z.1, x)) z.2)
    ContDiffOn ℝ ∞ R O ∧
      ∀ r ≤ j, ∀ z ∈ S, tau ^ r * ‖iteratedFDeriv ℝ r R z‖ ≤
        (2 ^ j * (2 * M1 * M2 + M2 ^ 2)) * (delta ^ 3 / tau) := by
  intro R
  let A := fun z : Ep × D => fderiv ℝ (fun x => U (z.1, x)) z.2
  let B := fun z : Ep × D => fderiv ℝ (fun x => W (z.1, x)) z.2
  let T := fun z : Ep × D => actualMetricJetPairing (A z) (B z) +
    actualMetricJetPairing (B z) (A z) + actualSpatialMetric (B z)
  have hA := (incrementsJointSpatialJets_bridge U O hO hU).2.1
  have hB := (incrementsJointSpatialJets_bridge W O hO hW).2.1
  have hAb : ∀ r ≤ j, ∀ z ∈ S, tau ^ r * ‖iteratedFDeriv ℝ r A z‖ ≤ M1 * delta := by
    intro r hr z hz
    have hb := actual_fast_spatial_first_weighted_jets U O S hO hSO hU j tau
      (M1 * delta * tau) htau hUb r hr z hz
    simpa only [mul_div_cancel_right₀ _ htau.ne'] using hb
  have hBb := actual_fast_spatial_first_weighted_jets W O S hO hSO hW j tau
    (M2 * delta ^ 2) htau hWb
  obtain ⟨hT, hTb⟩ := actual_metric_cross_self_weighted_jets A B O S hO hSO hA hB j
    tau (M1 * delta) (M2 * delta ^ 2 / tau) htau.le (by positivity) (by positivity) hAb hBb
  have he : EqOn R T O := actual_spatial_metric_displacement_add U W O hO hU hW
  refine ⟨hT.congr he, ?_⟩
  intro r hr z hz
  have hg : R =ᶠ[𝓝 z] T := by
    filter_upwards [hO.mem_nhds (hSO hz)] with w hw
    exact he hw
  rw [(hg.iteratedFDeriv ℝ r).eq_of_nhds]
  apply (hTb r hr z hz).trans
  have hpoly : 2 * (M1 * delta) * (M2 * delta ^ 2 / tau) + (M2 * delta ^ 2 / tau) ^ 2 ≤
      (2 * M1 * M2 + M2 ^ 2) * (delta ^ 3 / tau) := by
    have heq : (2 * M1 * M2 + M2 ^ 2) * (delta ^ 3 / tau) -
        (2 * (M1 * delta) * (M2 * delta ^ 2 / tau) + (M2 * delta ^ 2 / tau) ^ 2) =
        M2 ^ 2 * delta ^ 3 * (tau - delta) / tau ^ 2 := by
      field_simp [htau.ne']
      ring
    have hn : 0 ≤ M2 ^ 2 * delta ^ 3 * (tau - delta) / tau ^ 2 := by
      positivity
    linarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ (2 : ℝ) ^ j)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_fast_spatial_first_weighted_jets
#print axioms GlobalEmbedding.Continuation.actual_spatial_metric_displacement_add
#print axioms GlobalEmbedding.Continuation.actual_secondary_metric_remainder_weighted_jets
