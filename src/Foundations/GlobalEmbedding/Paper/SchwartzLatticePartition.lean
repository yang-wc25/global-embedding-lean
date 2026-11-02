import GlobalEmbedding.Paper.SchwartzLatticePeriodization
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Filter Set Metric
open scoped SchwartzMap Topology ContDiff

namespace GlobalEmbedding.Paper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A discrete lattice with a bounded actual fundamental-cover radius admits a nonnegative
compactly supported smooth partition function whose actual lattice sum is one. Choose a
bump equal to one on that radius, periodize it to a smooth positive periodic denominator,
and divide. This is a genuine Schwartz function, not an assumed partition oracle. -/
theorem exists_schwartz_lattice_partition
    (L : Submodule ℤ E) [DiscreteTopology L] {R : ℝ} (hR : 0 ≤ R)
    (hcover : ∀ x : E, ∃ z : L, ‖x + z‖ ≤ R) :
    ∃ χ : 𝓢(E, ℝ), HasCompactSupport (χ : E → ℝ) ∧ (∀ x, 0 ≤ χ x) ∧
      ∀ x, schwartzLatticePeriodization L χ x = 1 := by
  let φ : ContDiffBump (0 : E) :=
    { rIn := R + 1
      rOut := R + 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let g : 𝓢(E, ℝ) := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  let P : E → ℝ := schwartzLatticePeriodization L g
  have hr := schwartz_lattice_periodization_regular L g
  have hs (x : E) : Summable (fun z : L => g (x + z)) := by
    obtain ⟨v, hv, hb⟩ := schwartz_lattice_jet_majorant L g 0 (norm_nonneg x)
    exact Summable.of_norm_bounded hv (fun z => by simpa using hb z x le_rfl)
  have hp (x : E) : 0 < P x := by
    obtain ⟨z, hz⟩ := hcover x
    have hone : g (x + z) = 1 := φ.one_of_mem_closedBall (by
      simpa only [mem_closedBall, dist_zero_right] using (hz.trans (by dsimp [φ]; linarith)))
    have H : g (x + z) ≤ P x := (hs x).le_tsum z (fun w _ => φ.nonneg)
    rw [hone] at H
    exact zero_lt_one.trans_le H
  have hχ : ContDiff ℝ ∞ (fun x => g x / P x) :=
    g.smooth (⊤ : ℕ∞) |>.div hr.1 (fun x => (hp x).ne')
  have hc : HasCompactSupport (fun x => g x / P x) := by
    apply φ.hasCompactSupport.mono
    intro x hx
    change φ x ≠ 0
    intro hz
    apply hx
    change φ x / P x = 0
    rw [hz, zero_div]
  let χ : 𝓢(E, ℝ) := hc.toSchwartzMap hχ
  refine ⟨χ, hc, fun x => div_nonneg φ.nonneg (hp x).le, fun x => ?_⟩
  change (∑' z : L, g (x + z) / P (x + z)) = 1
  have he (z : L) : P (x + z) = P x := hr.2.2 z x
  simp_rw [he]
  rw [tsum_div_const]
  exact div_self (hp x).ne'

#print axioms exists_schwartz_lattice_partition

end GlobalEmbedding.Paper
