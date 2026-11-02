import GlobalEmbedding.Paper.PeriodicFlatTorusDistance

/-!
# Translation invariance of the actual flat torus distance

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
lines 382–418. DAG node: `balanced-holder-flat-translation-distance`.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- Translating two Euclidean lifts simultaneously preserves their actual flat torus distance.

Proof: coordinate projection to period-one quotient circles preserves addition. On the L2
product, addition of the same projected shift preserves distance by the normed additive-group
metric. Source: `lem:balanced`, periodic Hölder translation argument. -/
theorem periodic_flat_translation_distance {a : ℕ}
    (x y h : EuclideanSpace ℝ (Fin a)) :
    dist (toLp 2 (fun i : Fin a ↦ ((x + h) i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ ((y + h) i : AddCircle (1 : ℝ)))) =
      dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) := by
  have hadd (z : EuclideanSpace ℝ (Fin a)) :
      toLp 2 (fun i : Fin a ↦ ((z + h) i : AddCircle (1 : ℝ))) =
        toLp 2 (fun i : Fin a ↦ (z i : AddCircle (1 : ℝ))) +
          toLp 2 (fun i : Fin a ↦ (h i : AddCircle (1 : ℝ))) := by
    ext i
    simp
  rw [hadd x, hadd y, dist_add_right]

#print axioms periodic_flat_translation_distance

end GlobalEmbedding.Paper
