import Smoothing.ParameterRound2CrossInputJets
import GlobalEmbedding.Offline.OneStepScaleBounds

/-!
# Literal repair stage scales for the actual smoothing tail

The original r=q=40(k+1), ell=t^(11/10), tau=t^(6/5) give exactly the
two displayed integer powers below. This module also supplies native
joint subtraction regularity without adding a tensor-smoothness premise.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation
noncomputable section

theorem parameterRound2_repair_smoothing_powers {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (t^(11/10 : ℝ)/t)^(40*(k+1)) = t^(4*(k+1)) ∧
      (t^(6/5 : ℝ)/t)^(40*(k+1)) = t^(8*(k+1)) := by
  have hratio := repair_step_scale_ratios ht
  constructor
  · rw [hratio.2.1, ← Real.rpow_mul_natCast ht.le, ← Real.rpow_natCast t (4*(k+1))]
    congr 1
    push_cast
    ring
  · rw [hratio.1, ← Real.rpow_mul_natCast ht.le, ← Real.rpow_natCast t (8*(k+1))]
    congr 1
    push_cast
    ring

variable {E H X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem parameterRound2_native_sub_contMDiff
    (f g : X → Y) (hf : ContMDiff I 𝓘(ℝ,Y) ∞ f) (hg : ContMDiff I 𝓘(ℝ,Y) ∞ g) :
    ContMDiff I 𝓘(ℝ,Y) ∞ (fun x => f x-g x) := by
  have hp : ContMDiff I 𝓘(ℝ,Y×Y) ∞ (fun x => (f x,g x)) := hf.prodMk_space hg
  exact ((contDiff_fst.sub contDiff_snd : ContDiff ℝ ∞
    (fun z : Y×Y => z.1-z.2)).contMDiff.comp hp)

#print axioms parameterRound2_repair_smoothing_powers
#print axioms parameterRound2_native_sub_contMDiff
end
end GlobalEmbedding.Continuation
