import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslate
import GlobalEmbedding.Paper.PeriodicFlatTorusProjection

/-!
# Actual torus-parameter isometries of little periodic Hölder space

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-torus-translation`.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- An actual flat torus shift acts on the actual little Hölder space by a real linear isometry.

Choose a Euclidean representative using the proved surjectivity of the actual flat projection,
then use the constructed little-space translation. Independence of the representative and
continuity are separate named theorems. Source: translation in the proof of `lem:balanced`. -/
noncomputable def littlePeriodicCAlphaTorusTranslate {a N k : ℕ} {α : ℝ}
    (h : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) :
    LittlePeriodicCAlphaFunction a N k α →ₗᵢ[ℝ] LittlePeriodicCAlphaFunction a N k α :=
  littlePeriodicCAlphaTranslateIsometry ((periodic_flat_torus_projection.surjective h).choose)

#print axioms littlePeriodicCAlphaTorusTranslate

end GlobalEmbedding.Paper
