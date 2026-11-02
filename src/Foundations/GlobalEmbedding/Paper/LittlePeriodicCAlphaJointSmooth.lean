import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslate
import GlobalEmbedding.Paper.CollarLittleHolderEvaluation

/-!
# Joint source smoothness from actual norm-smooth translated little Hölder families

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–425.
DAG node: `balanced-holder-joint-smooth-from-orbit`.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- A norm-smooth actual translated little Hölder family has a genuinely jointly smooth lift.

Compose with the actual bounded evaluation at the fiber origin. Its value on translation by
h is exactly the original lift at h. Source: recovery of joint base/fiber regularity in the
proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_joint_smooth_of_orbit
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {a N k : ℕ} {α : ℝ}
    (U : Set P) (v : P → LittlePeriodicCAlphaFunction a N k α)
    (hv : ContDiffOn ℝ ∞ (fun z : P × EuclideanSpace ℝ (Fin a) ↦
      littlePeriodicCAlphaTranslateIsometry z.2 (v z.1))
      (U ×ˢ (univ : Set (EuclideanSpace ℝ (Fin a))))) :
    ContDiffOn ℝ ∞ (fun z : P × EuclideanSpace ℝ (Fin a) ↦ (v z.1).val.toFun z.2)
      (U ×ˢ (univ : Set (EuclideanSpace ℝ (Fin a)))) := by
  obtain ⟨ev, hev, hbound⟩ := collar_little_holder_evaluation (N := N) (k := k) (α := α) 0
  apply (ev.contDiff.comp_contDiffOn hv).congr
  intro z hz
  change (v z.1).val.toFun z.2 = ev (littlePeriodicCAlphaTranslateIsometry z.2 (v z.1))
  rw [hev]
  change (v z.1).val.toFun z.2 = (v z.1).val.toFun (0 + z.2)
  rw [zero_add]

#print axioms littlePeriodicCAlpha_joint_smooth_of_orbit

end GlobalEmbedding.Paper
