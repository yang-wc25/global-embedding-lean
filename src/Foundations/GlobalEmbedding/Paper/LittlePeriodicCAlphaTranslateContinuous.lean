import GlobalEmbedding.Paper.LittlePeriodicCAlphaSmoothOrbit
import GlobalEmbedding.Paper.LittlePeriodicCAlphaSmoothDense
import GlobalEmbedding.Paper.BalancedTranslationContinuousDense

/-!
# Joint continuity of the actual lifted little Hölder translation

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-lifted-translation-joint-continuity`.
-/

namespace GlobalEmbedding.Paper

/-- The actual Euclidean-lift translation action on the actual little Hölder space is jointly
continuous for α≤1.

Proof: use the actual isometries, density of actual smooth elements in the defining closure,
and the proved full-norm continuous smooth orbits in the generic dense-orbit theorem.
Source: smooth-closure translation argument in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_translate_joint_continuous {a N k : ℕ} {α : ℝ}
    (hα : α ≤ 1) :
    Continuous (fun z : EuclideanSpace ℝ (Fin a) × LittlePeriodicCAlphaFunction a N k α ↦
      littlePeriodicCAlphaTranslateIsometry z.1 z.2) := by
  apply balanced_translation_continuous_dense
    (fun h f ↦ littlePeriodicCAlphaTranslateIsometry h f)
    (fun h ↦ (littlePeriodicCAlphaTranslateIsometry h).isometry)
    _ (littlePeriodicCAlpha_smooth_dense a N k α)
  intro f hf
  exact littlePeriodicCAlpha_smooth_orbit_continuous f hf hα

#print axioms littlePeriodicCAlpha_translate_joint_continuous

end GlobalEmbedding.Paper
