import Probes.Round4ParameterScalePrefix
import Repair.EntranceNumeric

/-!
# The uniform reference envelope gives a genuine smaller entrance

Increasing the allowed reference tensor norm decreases the numerical
block scale.  Consequently the entrance computed before a particular
reference map is no larger than the scale of its actual repair block.
Only the two displayed finite orders of the actual metric are compared.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

theorem repairEntrance_numerical_scale_reference_antitone
    (m d N k : ℕ) (Cs Cmap Cmetric actual envelope : ℕ → ℝ)
    (Theta budget epsilon eta : ℝ)
    (hCs : ∀ j, 0 ≤ Cs j) (hCmap : ∀ j, 0 ≤ Cmap j)
    (hCmetric : ∀ j, 0 ≤ Cmetric j) (hactual : ∀ j, 0 ≤ actual j)
    (hbudget : 0 ≤ budget)
    (hCurrent : actual (40*(k+1)) ≤ envelope (40*(k+1)))
    (hNext : actual (40*(k+2)) ≤ envelope (40*(k+2))) :
    round4ParameterNumericalBlockScale m d N Cs Cmap Cmetric envelope Theta budget epsilon eta k ≤
      round4ParameterNumericalBlockScale m d N Cs Cmap Cmetric actual Theta budget epsilon eta k := by
  let Cpair := round3RepairClosedPairCost (m := m) (d := d) (N := N) Cs Cmap Cmetric
  have hCpair (j : ℕ) : 0 ≤ Cpair j := by
    exact add_nonneg
      (add_nonneg (add_nonneg (hCmetric j) (hCs j))
        (mul_nonneg (mul_nonneg (actualRepairCrossCost_nonneg (m+1) d N j) (hCs j)) (hCmap j)))
      (mul_nonneg (by positivity) (hCmap (j+1)))
  let rate := fun r : ℕ → ℝ => fun j : ℕ => 1+j*r j+2*Cpair j*(1+budget)
  have hRate (j : ℕ) : 0 ≤ rate actual j := by
    dsimp only [rate]
    have := hactual j
    have := hCpair j
    positivity
  have hRateLe (j : ℕ) (hj : actual j ≤ envelope j) : rate actual j ≤ rate envelope j := by
    dsimp only [rate]
    exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hj (by positivity))) le_rfl
  have hMax : max (rate actual (40*(k+1))) (rate actual (40*(k+2))) ≤
      max (rate envelope (40*(k+1))) (rate envelope (40*(k+2))) :=
    max_le_max (hRateLe _ hCurrent) (hRateLe _ hNext)
  have hMax0 : 0 ≤ max (rate actual (40*(k+1))) (rate actual (40*(k+2))) :=
    (hRate _).trans (le_max_left _ _)
  have hDen0 : 0 < 4*(max (rate actual (40*(k+1))) (rate actual (40*(k+2)))*(1+budget)+1) := by
    positivity
  have hDenLe : 4*(max (rate actual (40*(k+1))) (rate actual (40*(k+2)))*(1+budget)+1) ≤
      4*(max (rate envelope (40*(k+1))) (rate envelope (40*(k+2)))*(1+budget)+1) := by
    gcongr
  have hDiv : budget/(4*(max (rate envelope (40*(k+1))) (rate envelope (40*(k+2)))*(1+budget)+1)) ≤
      budget/(4*(max (rate actual (40*(k+1))) (rate actual (40*(k+2)))*(1+budget)+1)) :=
    div_le_div_of_nonneg_left hbudget hDen0 hDenLe
  have hDiv0 : 0 ≤ budget/(4*(max (rate envelope (40*(k+1))) (rate envelope (40*(k+2)))*(1+budget)+1)) :=
    div_nonneg hbudget (hDen0.le.trans hDenLe)
  have hPow := pow_le_pow_left₀ hDiv0 hDiv 5
  exact min_le_min (min_le_min le_rfl (min_le_min le_rfl (min_le_min hPow le_rfl))) le_rfl

theorem repairEntrance_numerical_scale_positive
    (m d N k : ℕ) (Cs Cmap Cmetric reference : ℕ → ℝ)
    (Theta budget epsilon eta : ℝ)
    (hCs : ∀ j, 0 ≤ Cs j) (hCmap : ∀ j, 0 ≤ Cmap j)
    (hCmetric : ∀ j, 0 ≤ Cmetric j) (hRef : ∀ j, 0 ≤ reference j)
    (hTheta : 0 < Theta) (hbudget : 0 < budget) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    0 < round4ParameterNumericalBlockScale m d N Cs Cmap Cmetric reference Theta budget epsilon eta k := by
  let Cd := round3RepairClosedTensorCost (m := m) (d := d) (N := N) Cs Cmap Cmetric
  let Cpair := round3RepairClosedPairCost (m := m) (d := d) (N := N) Cs Cmap Cmetric
  have hCd (j : ℕ) : 0 ≤ Cd j :=
    add_nonneg (add_nonneg (hCmetric j) (hCs j))
      (mul_nonneg (mul_nonneg (actualRepairCrossCost_nonneg (m+1) d N j) (hCs j)) (hCmap j))
  have hCpair (j : ℕ) : 0 ≤ Cpair j :=
    add_nonneg (hCd j) (mul_nonneg (by positivity) (hCmap (j+1)))
  let rate := fun j : ℕ => 1+j*reference j+2*Cpair j*(1+budget)
  have hRate (j : ℕ) : 0 ≤ rate j := by
    dsimp only [rate]
    have := hRef j
    have := hCpair j
    positivity
  have hMax : 0 ≤ max (rate (40*(k+1))) (rate (40*(k+2))) :=
    (hRate _).trans (le_max_left _ _)
  change 0 < min (min ((1/2 : ℝ)^5) (min (epsilon/(8*(Cmap (k/2)+1)))
    (min ((budget/(4*(max (rate (40*(k+1))) (rate (40*(k+2)))*(1+budget)+1)))^5)
      ((eta/(2*Cd 0*(1+budget)^2+1))^5)))) (Theta^10/2)
  have := hCmap (k/2)
  have := hCd 0
  positivity

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

/-- The actual block always admits the entrance computed with a numerical
upper envelope; the source, parameter and all original norm domains are
unchanged. -/
theorem repairEntrance_envelope_scale_le_actual
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (Cs envelope : ℕ → ℝ) (cost : Round3RepairPrimitiveCosts)
    (budget epsilon eta cap : ℝ) (k : ℕ)
    (hCs : ∀ j, 0 ≤ Cs j) (hbudget : 0 ≤ budget)
    (hCurrent : packet.closedReferenceProfile (40*(k+1)) ≤ envelope (40*(k+1)))
    (hNext : packet.closedReferenceProfile (40*(k+2)) ≤ envelope (40*(k+2))) :
    min (round4ParameterNumericalBlockScale m d N Cs cost.Cmap cost.Cmetric envelope
      cost.Theta budget epsilon eta k) (cap/2) ≤
    min (round4ParameterBlockScale packet Cs cost budget epsilon eta k) (cap/2) := by
  rw [round4ParameterBlockScale_eq_numerical]
  apply min_le_min _ le_rfl
  exact repairEntrance_numerical_scale_reference_antitone m d N k Cs cost.Cmap cost.Cmetric
    packet.closedReferenceProfile envelope cost.Theta budget epsilon eta hCs cost.map_nonneg
    cost.metric_nonneg (fun _ => ENNReal.toReal_nonneg) hbudget hCurrent hNext

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntrance_numerical_scale_reference_antitone
#print axioms GlobalEmbedding.Continuation.repairEntrance_numerical_scale_positive
#print axioms GlobalEmbedding.Continuation.repairEntrance_envelope_scale_le_actual
