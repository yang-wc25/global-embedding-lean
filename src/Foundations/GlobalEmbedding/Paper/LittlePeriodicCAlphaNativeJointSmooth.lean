import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusValueLift
import GlobalEmbedding.Paper.LittlePeriodicCAlphaJointSmooth
import GlobalEmbedding.Paper.PeriodicFlatTorusProductLiftOn

/-!
# Native joint parameter/fiber smoothness from actual norm-smooth little Hölder orbits

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-native-joint-smooth-from-orbit`.
-/

open Set
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Genuine norm-smooth actual translated families give native joint C∞ on the actual torus.

Bounded evaluation recovers actual joint lift smoothness from the norm-smooth orbit. The
proved every-lift value identity identifies this lift with actual torus evaluation. Apply
the genuine parameter-times-torus smooth lifting criterion for the actual original torus
atlas. No underlying native smoothness is assumed. Source: joint base/fiber regularity
recovery in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_native_joint_smooth_of_orbit
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {a N k : ℕ} {α : ℝ}
    (U : Set P) (hU : IsOpen U) (v : P → LittlePeriodicCAlphaFunction a N k α)
    (hv : ContDiffOn ℝ ∞ (fun z : P × EuclideanSpace ℝ (Fin a) ↦
      littlePeriodicCAlphaTranslateIsometry z.2 (v z.1)) (U ×ˢ univ)) :
    let _charted := periodicFlatTorusChartedSpace a
    ContMDiffOn ((𝓘(ℝ, P)).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin a))))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin N))) ∞
      (fun z : P × PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)) ↦
        littlePeriodicCAlphaTorusValue (v z.1) z.2) (U ×ˢ univ) := by
  dsimp only
  let _charted := periodicFlatTorusChartedSpace a
  apply (periodic_flat_torus_product_lift_contMDiffOn_iff ∞ U hU _).mpr
  simpa only [littlePeriodicCAlphaTorusValue_lift] using
    littlePeriodicCAlpha_joint_smooth_of_orbit U v hv

#print axioms littlePeriodicCAlpha_native_joint_smooth_of_orbit

end GlobalEmbedding.Paper
