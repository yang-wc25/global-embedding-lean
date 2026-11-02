import GlobalEmbedding.Offline.CompactGoodDictionaryTemplates
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Normed.Group.Basic

/-!
# One fixed parameter ball, then one scale, for a finite probe list

All constants belong to the selected finite wave dictionary.  The parameter
radius is chosen before the scale threshold, precisely as in (8.2) and the
compact incidence preparation in `thm:upgrade`.  Empty finite lists are allowed.
The proof reuses the earlier finite positive common-lower-bound lemma.
-/

open Filter Set GlobalEmbedding.Offline
open scoped Topology

namespace GlobalEmbedding.Upgrade

/-- Simultaneously put every `η(t)+C|u|` remainder below its own positive
geometric margin.  This chooses a genuine fixed ball, not a ball shrinking
with `t`, and the conclusion holds for every parameter in that ball. -/
theorem finite_probe_parameter_ball_then_scale
    {ι U : Type*} [Fintype ι] [NormedAddCommGroup U]
    (η : ι → ℝ → ℝ) (C margin : ι → ℝ)
    (hη : ∀ i, Tendsto (η i) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hmargin : ∀ i, 0 < margin i) :
    ∃ ρ > 0, ∃ t0 > 0,
      ∀ t, 0 < t → t < t0 → ∀ u : U, ‖u‖ < ρ →
        ∀ i, |η i t| + |C i| * ‖u‖ < margin i := by
  obtain ⟨ρ, hρ, hρle⟩ := finite_positive_common_lower_bound
    (fun i ↦ margin i / (4 * (|C i| + 1)))
    (fun i ↦ div_pos (hmargin i) (by positivity))
  have hsmall (i : ι) : ∀ᶠ t in 𝓝[>] (0 : ℝ), |η i t| < margin i / 2 := by
    have h := (hη i).norm
    have hlt : ‖(0 : ℝ)‖ < margin i / 2 := by simpa using half_pos (hmargin i)
    simpa only [Real.norm_eq_abs] using (tendsto_order.mp h).2 _ hlt
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, |η i t| < margin i / 2 :=
    Filter.eventually_all.mpr hsmall
  obtain ⟨t0, ht0, htime⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hall
  refine ⟨ρ, hρ, t0, ht0, ?_⟩
  intro t ht ht0' u hu i
  have hηbound := htime ⟨ht, ht0'⟩ i
  have hden : 0 < 4 * (|C i| + 1) := by positivity
  have hρbound := (le_div_iff₀ hden).mp (hρle i)
  have hmul := mul_lt_mul_of_pos_left hu (show 0 < |C i| + 1 by positivity)
  have hnorm := norm_nonneg u
  have hC := abs_nonneg (C i)
  nlinarith

end GlobalEmbedding.Upgrade
