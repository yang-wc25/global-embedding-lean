import NormalPolar.ActualProbeInitialSupplyReferenceTarget

/-! The actual first target is a small displacement of the original canonical
center.  The target is not silently identified with the reference metric.
A fixed positive scale cap places it in half the original reserve ball, so
canonical raw suppliers may be recentered without changing any fields. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Topology Classical
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference Given : ℕ → ℝ}

theorem actualProbeInitialSupply_target_difference
    (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
    (hmetric : packet.metric = Data.H) (t : ℝ) (ht : 0 < t) :
    actualProbeInitialTargetGerm packet hmetric t - actualProbeInitialReferenceGerm packet hmetric =
      (-(t^4)) • actualProbeInitialReferenceGerm packet hmetric := by
  have htau : (t^((6 : ℝ)/5))^10 = t^12 := by
    rw [← Real.rpow_natCast (t^((6 : ℝ)/5)) 10,
      ← Real.rpow_mul ht.le]
    norm_num
  have hratio : (t^((6 : ℝ)/5))^10/(t^10) = t^2 := by
    rw [htau]
    field_simp
  change (1-((t^((6 : ℝ)/5))^10/(t^10))^2) • _ - _ = _
  rw [hratio]
  symm
  calc
    (-(t^4)) • actualProbeInitialReferenceGerm packet hmetric =
      ((1-(t^2)^2)-1) • actualProbeInitialReferenceGerm packet hmetric := by
        congr 1
        ring
    _ = _ := by rw [sub_smul,one_smul]

theorem actualProbeInitialSupply_target_center_bound
    (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
    (hmetric : packet.metric = Data.H) (t : ℝ) (ht : 0 < t)
    (ell : ℝ) (hell1 : ell ≤ 1) (j : ℕ) :
    parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples
      univ packet.closedSamples_compact (fun _ _ hy => hy.1) ell j
      (actualProbeInitialTargetGerm packet hmetric t - actualProbeInitialReferenceGerm packet hmetric) ≤
      t^4 * actualProbeInitialReferenceProfile packet hmetric j := by
  rw [actualProbeInitialSupply_target_difference packet hmetric t ht,
    map_smul_eq_mul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (pow_nonneg ht.le 4)]
  have hmono := actualProbeInitialSupply_reference_scaled_profile packet hmetric 1 ell
    (by norm_num) le_rfl hell1 j
  simp only [one_smul] at hmono
  exact mul_le_mul_of_nonneg_left hmono (pow_nonneg ht.le _)

theorem actualProbeInitialSupply_target_center_threshold
    (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
    (hmetric : packet.metric = Data.H) (rho : ℝ) (hrho : 0 < rho) :
    ∃ t0 : ℝ, 0 < t0 ∧ t0 ≤ 1 ∧ ∀ t : ℝ, 0 < t → t ≤ t0 →
      ∀ ell : ℝ, ell ≤ 1 →
      parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples
        univ packet.closedSamples_compact (fun _ _ hy => hy.1) ell 0
        (actualProbeInitialTargetGerm packet hmetric t - actualProbeInitialReferenceGerm packet hmetric) ≤ rho/2 := by
  let H0 := actualProbeInitialReferenceProfile packet hmetric 0
  have hH0 : 0 ≤ H0 := apply_nonneg _ _
  let t0 := min 1 (rho/(2*(H0+1)))
  have ht0 : 0 < t0 := lt_min (by norm_num) (div_pos hrho (by positivity))
  refine ⟨t0,ht0,min_le_left _ _,?_⟩
  intro t ht htt ell hell1
  have ht1 : t ≤ 1 := htt.trans (min_le_left _ _)
  have htCap : t ≤ rho/(2*(H0+1)) := htt.trans (min_le_right _ _)
  have hpower : t^4 ≤ t := by
    calc
      t^4 ≤ t^1 := pow_le_pow_of_le_one ht.le ht1 (by omega)
      _ = t := pow_one _
  have hsmall : t*H0 ≤ rho/2 := by
    have hden : 0 < 2*(H0+1) := by positivity
    have hprod := (le_div_iff₀ hden).mp htCap
    nlinarith
  exact (actualProbeInitialSupply_target_center_bound packet hmetric t ht ell hell1 0).trans
    ((mul_le_mul_of_nonneg_right hpower hH0).trans hsmall)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_target_difference
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_target_center_bound
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_target_center_threshold
