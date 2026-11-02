import NormalPolar.PassiveOriginalRawAtlas
import NormalPolar.PassiveOriginalSamples
import Probes.ActualIncrementOriginalCoordinateJets

/-! The actual original core profile of the passive compact-parameter data
is bounded by the original seed profile with constant one, at every order
and every scale. The statement is about the literal original F, H, cutoff,
normal and spatial phase-covector fields and their actual original norm
domains. No final-wave estimate, smoothness beyond the original inputs, or
change to the original coordinate norm is assumed. Parameter-chart
transition costs are deliberately outside this core statement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper

variable {n d N q : ℕ} {M S P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [Subsingleton S] [TopologicalSpace P]

variable (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
  (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
  (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
  (b₀ : Fin seed.parameterCount)
  (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
  (hQ₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ seed.parameterNormDomain b₀)
  (hs₀ : s₀ ∈ seed.parameterSet)

include hb₀ hQ₀ hs₀ in
theorem passiveOriginal_full_weighted_le (base j : ℕ) (ell : ℝ)
    (f : (Fin seed.atlas.count × Fin seed.parameterCount) → (Fin n → ℝ) → Fin q → ℝ) :
    paperAtlasWeighted base j ell
      (fun i : Fin seed.atlas.count × Fin B.count =>
        f (i.1,b₀) ∘ passiveOriginalSourceProjection (d := d))
      (incrementsOriginalDifferentiation seed.atlas B.chart)
      (incrementsOriginalEvaluation seed.atlas B.chart seed.sourceNormDomain Q univ) ≤
    paperAtlasWeighted base j ell f
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart)
      (incrementsOriginalEvaluation seed.atlas seed.parameterChart seed.sourceNormDomain
        seed.parameterNormDomain seed.parameterSet) :=
  passiveOriginal_raw_paperAtlasWeighted_le (n := n) (d := d) (q := q)
    (ι := Fin seed.atlas.count × Fin seed.parameterCount)
    (κ := Fin seed.atlas.count × Fin B.count) base j ell f
    (incrementsOriginalDifferentiation seed.atlas seed.parameterChart)
    (incrementsOriginalEvaluation seed.atlas seed.parameterChart seed.sourceNormDomain
      seed.parameterNormDomain seed.parameterSet)
    (parameterRound2_originalDifferentiation_open seed.atlas seed.parameterChart)
    (fun i => (i.1,b₀))
    (incrementsOriginalDifferentiation seed.atlas B.chart)
    (incrementsOriginalEvaluation seed.atlas B.chart seed.sourceNormDomain Q univ)
    (parameterRound2_originalDifferentiation_open seed.atlas B.chart)
    (passiveOriginal_differentiation_projection seed B b₀ hb₀)
    (fun _ _ hy => hy.1)
    (passiveOriginal_evaluation_projection s₀ seed B Q b₀ hb₀ hQ₀ hs₀)

include hb₀ hQ₀ hs₀ in
theorem passiveOriginal_primary_weighted_le
    (hPrimary : ∀ l, IsOpen (seed.primaryDomain l)) (l : Fin seed.primaryCount)
    (base j : ℕ) (ell : ℝ)
    (f : (Fin seed.atlas.count × Fin seed.parameterCount) → (Fin n → ℝ) → Fin q → ℝ) :
    paperAtlasWeighted base j ell
      (fun i : Fin seed.atlas.count × Fin B.count =>
        f (i.1,b₀) ∘ passiveOriginalSourceProjection (d := d))
      (incrementsOriginalPrimaryDifferentiation (passiveOriginalData s₀ seed B Q) l)
      (incrementsOriginalPrimaryEvaluation (passiveOriginalData s₀ seed B Q) l) ≤
    paperAtlasWeighted base j ell f (incrementsOriginalPrimaryDifferentiation seed l)
      (incrementsOriginalPrimaryEvaluation seed l) := by
  apply passiveOriginal_raw_paperAtlasWeighted_le (n := n) (d := d) (q := q) base j ell f _ _
    (actual_original_primaryDifferentiation_open seed hPrimary l)
    (fun i : Fin seed.atlas.count × Fin B.count => (i.1,b₀))
  · exact actual_original_primaryDifferentiation_open (passiveOriginalData s₀ seed B Q)
      (fun l => (hPrimary l).preimage (continuous_const.prodMk continuous_snd)) l
  · exact passiveOriginal_primaryDifferentiation_projection s₀ seed B Q b₀ hb₀ l
  · intro i y hy
    exact ⟨hy.1.1,hy.2⟩
  · exact passiveOriginal_primaryEvaluation_projection s₀ seed B Q b₀ hb₀ hQ₀ hs₀ l

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) S]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin 0)) ∞ S]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

include hb₀ hQ₀ hs₀ in
/-- The same all-order, all-scale original core budget for the actual
passive native input, with no chosen output field among the hypotheses. -/
theorem passiveOriginal_core_profile_le
    (hPrimary : ∀ l, IsOpen (seed.primaryDomain l)) (j : ℕ) (ell : ℝ) :
    incrementsOriginalCoreInputProfile (passiveOriginalData s₀ seed B Q) j ell ≤
      incrementsOriginalCoreInputProfile seed j ell := by
  have hF : incrementsOriginalMapCoordinates seed.atlas B.chart
      (fun z => seed.F (s₀,z.2)) =
      fun i => incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F (i.1,b₀)
        ∘ passiveOriginalSourceProjection (d := d) := by
    funext i y
    exact passiveOriginal_mapCoordinates s₀ seed B b₀ seed.F i y
  have hH : incrementsOriginalTensorCoordinates seed.atlas B.chart
      (fun _ => seed.H s₀) =
      fun i => incrementsOriginalTensorCoordinates seed.atlas seed.parameterChart seed.H (i.1,b₀)
        ∘ passiveOriginalSourceProjection (d := d) := by
    funext i y
    exact passiveOriginal_tensorCoordinates s₀ seed B b₀ seed.H i y
  unfold incrementsOriginalCoreInputProfile
  dsimp only
  apply max_le_max
  · change paperAtlasWeighted 2 j ell
      (incrementsOriginalMapCoordinates seed.atlas B.chart (fun z => seed.F (s₀,z.2))) _ _ ≤ _
    rw [hF]
    exact passiveOriginal_full_weighted_le s₀ seed B Q b₀ hb₀ hQ₀ hs₀ 2 j ell _
  · apply max_le_max
    · change paperAtlasWeighted 0 j ell
        (incrementsOriginalTensorCoordinates seed.atlas B.chart (fun _ => seed.H s₀)) _ _ ≤ _
      rw [hH]
      exact passiveOriginal_full_weighted_le s₀ seed B Q b₀ hb₀ hQ₀ hs₀ 0 j ell _
    · apply iSup_mono
      intro l
      change Fin seed.primaryCount at l
      have hc : incrementsOriginalScalarCoordinates (passiveOriginalData s₀ seed B Q)
          (fun z => seed.cutoff l (s₀,z.2)) =
          fun i => incrementsOriginalScalarCoordinates seed (seed.cutoff l) (i.1,b₀)
            ∘ passiveOriginalSourceProjection (d := d) := by
        funext i y
        exact passiveOriginal_scalarCoordinates s₀ seed B Q b₀ (seed.cutoff l) i y
      have hn : incrementsOriginalMapCoordinates seed.atlas B.chart
          (fun z => seed.freeNormal l (s₀,z.2)) =
          fun i => incrementsOriginalMapCoordinates seed.atlas seed.parameterChart
            (seed.freeNormal l) (i.1,b₀) ∘ passiveOriginalSourceProjection (d := d) := by
        funext i y
        exact passiveOriginal_mapCoordinates s₀ seed B b₀ (seed.freeNormal l) i y
      have hp : incrementsOriginalPhaseCovectorCoordinates (passiveOriginalData s₀ seed B Q) l =
          fun i => incrementsOriginalPhaseCovectorCoordinates seed l (i.1,b₀)
            ∘ passiveOriginalSourceProjection (d := d) := by
        funext i y
        exact passiveOriginal_phaseCovectorCoordinates s₀ seed B Q b₀ l i y
      apply max_le_max
      · change paperAtlasWeighted 0 j ell
          (incrementsOriginalScalarCoordinates (passiveOriginalData s₀ seed B Q)
            (fun z => seed.cutoff l (s₀,z.2))) _ _ ≤ _
        rw [hc]
        exact passiveOriginal_primary_weighted_le s₀ seed B Q b₀ hb₀ hQ₀ hs₀ hPrimary l 0 j ell _
      · apply max_le_max
        · change paperAtlasWeighted 0 j ell
            (incrementsOriginalMapCoordinates seed.atlas B.chart
              (fun z => seed.freeNormal l (s₀,z.2))) _ _ ≤ _
          rw [hn]
          exact passiveOriginal_primary_weighted_le s₀ seed B Q b₀ hb₀ hQ₀ hs₀ hPrimary l 0 j ell _
        · rw [hp]
          exact passiveOriginal_primary_weighted_le s₀ seed B Q b₀ hb₀ hQ₀ hs₀ hPrimary l 0 j ell _

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_core_profile_le
