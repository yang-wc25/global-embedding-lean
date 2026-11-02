import NormalPolar.ActualRepairModelSameRun

/-!
# Nonnegative full-domain moduli for the actual repair response

The original probe record asks for nonnegativity at every real scale, while
only positive scales are admitted geometrically. Absolute-value extensions
agree with the established same-run bounds on that entire original admitted
domain, and satisfy the full real-domain modulus contract.
-/
noncomputable section
open Filter GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Continuation
open scoped Topology
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks

def actualRepairModelHessianModulus (C t : ℝ) : ℝ := 2*C*|t|^(8/25 : ℝ)
def actualRepairModelCOneModulus (C t : ℝ) : ℝ := 2*C*|t|^(14/25 : ℝ)
def actualRepairModelValueModulus (C t : ℝ) : ℝ := 2*C*|t|^(4/5 : ℝ)

theorem actualRepairModel_moduli_nonneg {C : ℝ} (hC : 0 ≤ C) (t : ℝ) :
    0 ≤ actualRepairModelHessianModulus C t ∧
    0 ≤ actualRepairModelCOneModulus C t ∧
    0 ≤ actualRepairModelValueModulus C t := by
  unfold actualRepairModelHessianModulus actualRepairModelCOneModulus actualRepairModelValueModulus
  exact ⟨by positivity,by positivity,by positivity⟩

theorem actualRepairModel_moduli_eq_original {C t : ℝ} (ht : 0 ≤ t) :
    actualRepairModelHessianModulus C t = round4RepairHessianTailModulus C t ∧
    actualRepairModelCOneModulus C t = round4RepairCOneTailModulus C t ∧
    actualRepairModelValueModulus C t = round4RepairValueTailModulus C t := by
  simp only [actualRepairModelHessianModulus,actualRepairModelCOneModulus,
    actualRepairModelValueModulus,round4RepairHessianTailModulus,
    round4RepairCOneTailModulus,round4RepairValueTailModulus,abs_of_nonneg ht,and_self]

private theorem actualRepairModel_abs_power_tendsto (C q : ℝ) (hq : 0 < q) :
    Tendsto (fun t : ℝ => 2*C*|t|^q) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun t : ℝ => 2*C*|t|^q) :=
    continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr hq.le))
  have h : Tendsto (fun t : ℝ => 2*C*|t|^q) (𝓝[>] 0) (𝓝 (2*C*|0|^q)) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  simpa only [abs_zero,Real.zero_rpow hq.ne',mul_zero] using h

theorem actualRepairModel_moduli_tendsto (C : ℝ) :
    Tendsto (actualRepairModelHessianModulus C) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (actualRepairModelCOneModulus C) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (actualRepairModelValueModulus C) (𝓝[>] 0) (𝓝 0) :=
  ⟨actualRepairModel_abs_power_tendsto C _ (by norm_num),
    actualRepairModel_abs_power_tendsto C _ (by norm_num),
    actualRepairModel_abs_power_tendsto C _ (by norm_num)⟩

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_moduli_nonneg
#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_moduli_tendsto
