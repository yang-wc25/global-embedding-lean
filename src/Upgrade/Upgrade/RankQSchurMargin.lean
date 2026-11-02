import Upgrade.RankQSchurDifferential
import Upgrade.RankQSchurRank

/-!
# Genuine Schur-chart protection and derivative margin

Invertibility of the chosen actual q-block and closeness of the exact
nonlinear defining-equation derivative are consequences of the reference
form, not hypotheses on the incidence rank. The same radius is used for
both properties and supplies a uniform operator-norm bound for probe errors.
-/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace GlobalEmbedding.Upgrade

variable {S W : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [FiniteDimensional ℝ S] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- An actual norm ball protects the chosen q-block, its rank equation and
its exact derivative. This is the geometric margin used after the true
second form has been transported into the reference normal/source frame. -/
theorem rankQSchur_exists_margin (B : S →L[ℝ] W) (delta : ℝ) (hdelta : 0 < delta) :
    let : NormedAddCommGroup B.ker := inferInstance
    let : NormedSpace ℝ B.ker := inferInstance
    let : NormedAddCommGroup B.rangeᗮ := inferInstance
    let : NormedSpace ℝ B.rangeᗮ := inferInstance
    let : NormedAddCommGroup (B.ker →L[ℝ] B.rangeᗮ) := inferInstance
    let : NormedSpace ℝ (B.ker →L[ℝ] B.rangeᗮ) := inferInstance
    let : NormedAddCommGroup ((S →L[ℝ] W) →L[ℝ] (B.ker →L[ℝ] B.rangeᗮ)) := inferInstance
    let : NormedSpace ℝ ((S →L[ℝ] W) →L[ℝ] (B.ker →L[ℝ] B.rangeᗮ)) := inferInstance
    ∃ rho : ℝ, 0 < rho ∧ ∀ C : S →L[ℝ] W, ‖C - B‖ < rho →
      (rankQBlockA B C).IsInvertible ∧
      ContDiffAt ℝ ∞ (rankQSchur B) C ∧
      ‖fderiv ℝ (rankQSchur B) C - rankQNormalBlock B‖ < delta ∧
      ‖fderiv ℝ (rankQSchur B) C‖ ≤ ‖rankQNormalBlock B‖ + delta ∧
      (rankQSchur B C = 0 ↔ Module.finrank ℝ C.range = Module.finrank ℝ B.range) := by
  let : NormedAddCommGroup B.ker := inferInstance
  let : NormedSpace ℝ B.ker := inferInstance
  let : NormedAddCommGroup B.rangeᗮ := inferInstance
  let : NormedSpace ℝ B.rangeᗮ := inferInstance
  let : NormedAddCommGroup (B.ker →L[ℝ] B.rangeᗮ) := inferInstance
  let : NormedSpace ℝ (B.ker →L[ℝ] B.rangeᗮ) := inferInstance
  let : NormedAddCommGroup ((S →L[ℝ] W) →L[ℝ] (B.ker →L[ℝ] B.rangeᗮ)) := inferInstance
  let : NormedSpace ℝ ((S →L[ℝ] W) →L[ℝ] (B.ker →L[ℝ] B.rangeᗮ)) := inferInstance
  have hder : ∀ᶠ C in 𝓝 B,
      ‖fderiv ℝ (rankQSchur B) C - rankQNormalBlock B‖ < delta := by
    have hc : ContinuousAt
        (fun C : S →L[ℝ] W ↦ ‖fderiv ℝ (rankQSchur B) C - rankQNormalBlock B‖) B :=
      ((rankQSchur_continuousAt_fderiv B).sub continuousAt_const).norm
    have hval : ‖fderiv ℝ (rankQSchur B) B - rankQNormalBlock B‖ < delta := by
      simpa only [rankQSchur_fderiv_self, sub_self, norm_zero] using hdelta
    exact hc.eventually (isOpen_Iio.mem_nhds hval)
  obtain ⟨rho, hrho, hnear⟩ := Metric.eventually_nhds_iff.mp
    ((rankQBlockA_eventually_isInvertible B).and hder)
  refine ⟨rho, hrho, ?_⟩
  intro C hC
  have hpair := hnear (by simpa only [dist_eq_norm] using hC)
  have hbound : ‖fderiv ℝ (rankQSchur B) C‖ ≤ ‖rankQNormalBlock B‖ + delta := by
    have htri := norm_add_le
      (fderiv ℝ (rankQSchur B) C - rankQNormalBlock B) (rankQNormalBlock B)
    rw [sub_add_cancel] at htri
    linarith [hpair.2]
  exact ⟨hpair.1, rankQSchur_contDiffAt B C hpair.1, hpair.2, hbound,
    rankQSchur_eq_zero_iff_rank B C hpair.1⟩

end GlobalEmbedding.Upgrade
