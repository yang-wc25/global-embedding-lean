import NormalPolar.ActualRepairFinalBudgets

/-!
# Selecting the initial probe threshold from actual C2 convergence

The original existence statement leaves the scale threshold to be chosen.
This explicit choice is made from fixed reference and mapping constants,
before a probe record exists.  It proves the polar reserve from the genuine
C2 displacement.  It is not a restriction operation on an existing probe,
and it does not assume a reserve for the unknown normal identification.
-/

noncomputable section
open Set Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

def actualProbeReserveThreshold (initialThreshold K C : ℝ) : ℝ :=
  min initialThreshold ((1 / (2 * (K * C + 1))) ^ ((5 : ℝ) / 44))

theorem actualProbeReserveThreshold_pos
    {initialThreshold K C : ℝ} (hT : 0 < initialThreshold) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    0 < actualProbeReserveThreshold initialThreshold K C := by
  unfold actualProbeReserveThreshold
  apply lt_min hT
  apply Real.rpow_pos_of_pos
  positivity

theorem actualProbeReserveThreshold_le (initialThreshold K C : ℝ) :
    actualProbeReserveThreshold initialThreshold K C ≤ initialThreshold :=
  min_le_left _ _

/-- The chosen scale yields a real reserve of one half. -/
theorem actualProbeReserveThreshold_budget
    {initialThreshold K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (t : ℝ) (ht : 0 < t) (htt : t < actualProbeReserveThreshold initialThreshold K C) :
    K * (C * t ^ ((44 : ℝ) / 5)) ≤ (1 : ℝ) / 2 := by
  let epsilon : ℝ := 1 / (2 * (K * C + 1))
  have heps : 0 < epsilon := by unfold epsilon; positivity
  have hsmall : t ≤ epsilon ^ ((5 : ℝ) / 44) :=
    htt.le.trans (min_le_right _ _)
  have hpow : t ^ ((44 : ℝ) / 5) ≤ epsilon := by
    calc
      _ ≤ (epsilon ^ ((5 : ℝ) / 44)) ^ ((44 : ℝ) / 5) :=
        Real.rpow_le_rpow ht.le hsmall (by norm_num)
      _ = epsilon := by rw [← Real.rpow_mul heps.le]; norm_num
  have hden : 0 < 2 * (K * C + 1) := by positivity
  have hquot : K * C / (2 * (K * C + 1)) ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  calc
    K * (C * t ^ ((44 : ℝ) / 5)) = (K * C) * t ^ ((44 : ℝ) / 5) := by ring
    _ ≤ (K * C) * epsilon := mul_le_mul_of_nonneg_left hpow (mul_nonneg hK hC)
    _ = K * C / (2 * (K * C + 1)) := by simp only [epsilon, div_eq_mul_inv, one_mul]
    _ ≤ _ := hquot

variable {n N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [NormedAddCommGroup P]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- The tight reserve field is a consequence of actual final C2 convergence.
The parameter ball is unchanged and the same scalar bound is uniform on it. -/
theorem actual_probe_closeness_reserve_from_C2
    (A : BufferedAtlas M E) (F₀ : M → V) (F : ℝ → P → M → V)
    (radius initialThreshold K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hclose : ∀ t, 0 < t → t < initialThreshold → ∀ u, ‖u‖ < radius →
      probeAtlasCj A 2 (F t u - F₀) ≤ ENNReal.ofReal (C * t ^ ((44 : ℝ) / 5))) :
    ∀ t, 0 < t → t < actualProbeReserveThreshold initialThreshold K C →
      ∃ b : ℝ, 0 ≤ b ∧
        (∀ u, ‖u‖ < radius → probeAtlasCj A 2 (F t u - F₀) ≤ ENNReal.ofReal b) ∧
        K * b ≤ (1 : ℝ) / 2 := by
  intro t ht htt
  refine ⟨C * t ^ ((44 : ℝ) / 5), by positivity, ?_, ?_⟩
  · exact hclose t ht (htt.trans_le (actualProbeReserveThreshold_le initialThreshold K C))
  · exact actualProbeReserveThreshold_budget hK hC t ht htt

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualProbeReserveThreshold_budget
#print axioms GlobalEmbedding.NormalPolar.actual_probe_closeness_reserve_from_C2
