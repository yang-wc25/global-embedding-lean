import NormalPolar.PassiveOriginalCoordinateRows
import NormalPolar.PassiveOriginalProfile
import Probes.ActualOriginalPhaseProfileJets

/-! The total phase differential of the same literal passive input.
The scalar phase is first identified as the actual seed phase composed
with the original source projection; only then is it differentiated.
Parameter covector coordinates are genuinely zero, and every source
covector coordinate is retained. No phase output estimate is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation

def passiveOriginalCovectorSelect (n d : ℕ) : Fin (n+d) → Option (Fin n) :=
  Fin.addCases some (fun _ => none)

variable {n d N : ℕ} {M S P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [Subsingleton S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) S]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin 0)) ∞ S]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

variable (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
  (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
  (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
  (b₀ : Fin seed.parameterCount)

theorem passiveOriginal_jointPhase (l : Fin seed.primaryCount)
    (i : Fin seed.atlas.count × Fin B.count) :
    actualOriginalJointPhase (passiveOriginalData s₀ seed B Q) l i =
      actualOriginalJointPhase seed l (i.1,b₀) ∘ passiveOriginalSourceProjection := by
  funext y
  change seed.phase l (s₀,(incrementsOriginalJointPoint seed.atlas B.chart i y).2) =
    seed.phase l (incrementsOriginalJointPoint seed.atlas seed.parameterChart (i.1,b₀)
      (passiveOriginalSourceProjection y))
  rw [passiveOriginal_jointPoint s₀ seed B b₀]

theorem passiveOriginal_primary_phaseOpen_projection
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
    (hsOpen : s₀ ∈ seed.parameterOpen) (l : Fin seed.primaryCount)
    (i : Fin seed.atlas.count × Fin B.count) :
    MapsTo (passiveOriginalSourceProjection (d := d))
      (incrementsOriginalPrimaryDifferentiation (passiveOriginalData s₀ seed B Q) l i)
      (actualOriginalPhaseOpen seed l (i.1,b₀)) := by
  intro y hy
  have hmem := passiveOriginal_primaryDifferentiation_projection s₀ seed B Q b₀ hb₀ l i hy
  refine ⟨hmem,hmem.1,?_⟩
  change incrementsOriginalJointPoint seed.atlas seed.parameterChart (i.1,b₀)
      (passiveOriginalSourceProjection y) ∈ seed.parameterOpen ×ˢ univ
  rw [passiveOriginal_jointPoint s₀ seed B b₀]
  exact ⟨hsOpen,mem_univ _⟩

theorem passiveOriginal_totalPhase_rows
    (hd : IncrementsOriginalDomainConditions seed) (hs : IncrementsOriginalSmoothInputs seed)
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
    (hsOpen : s₀ ∈ seed.parameterOpen) (l : Fin seed.primaryCount)
    (i : Fin seed.atlas.count × Fin B.count) :
    EqOn (actualOriginalTotalPhaseCoordinates (passiveOriginalData s₀ seed B Q) l i)
      (passiveOriginalSelectRows (passiveOriginalCovectorSelect n d)
        (actualOriginalTotalPhaseCoordinates seed l (i.1,b₀) ∘ passiveOriginalSourceProjection))
      (incrementsOriginalPrimaryDifferentiation (passiveOriginalData s₀ seed B Q) l i) := by
  intro y hy
  let L := passiveOriginalSourceProjection (n := n) (d := d)
  have hmem := passiveOriginal_primary_phaseOpen_projection s₀ seed B Q b₀ hb₀ hsOpen l i hy
  have hG : DifferentiableAt ℝ (actualOriginalJointPhase seed l (i.1,b₀)) (L y) :=
    ((actualOriginalJointPhase_contDiffOn seed hd hs l (i.1,b₀)).contDiffAt
      ((actualOriginalPhaseOpen_open seed hd l (i.1,b₀)).mem_nhds hmem)).differentiableAt (by simp)
  have hderiv : fderiv ℝ (actualOriginalJointPhase (passiveOriginalData s₀ seed B Q) l i) y =
      (fderiv ℝ (actualOriginalJointPhase seed l (i.1,b₀)) (L y)).comp L := by
    rw [passiveOriginal_jointPhase s₀ seed B Q b₀]
    exact (hG.hasFDerivAt.comp y L.hasFDerivAt).fderiv
  funext r
  unfold actualOriginalTotalPhaseCoordinates
  rw [hderiv]
  refine Fin.addCases (fun r₀ => ?_) (fun r₁ => ?_) r
  · change (fderiv ℝ (actualOriginalJointPhase seed l (i.1,b₀)) (L y))
      (L (Pi.single (Fin.castAdd d r₀) 1)) = _
    simp only [L,passiveOriginalSourceProjection_single_source,passiveOriginalSelectRows,
      passiveOriginalCovectorSelect,Fin.addCases_left,Function.comp_apply,
      actualOriginalTotalPhaseCoordinates]
  · change (fderiv ℝ (actualOriginalJointPhase seed l (i.1,b₀)) (L y))
      (L (Pi.single (Fin.natAdd n r₁) 1)) = _
    simp only [L,passiveOriginalSourceProjection_single_parameter (Fin.natAdd n r₁) (by simp),
      map_zero,passiveOriginalSelectRows,passiveOriginalCovectorSelect,Fin.addCases_right]

/-- Constant one for the entire original total-phase covector profile,
including all parameter coordinate partials at every derivative order. -/
theorem passiveOriginal_totalPhase_weighted_le
    (hd : IncrementsOriginalDomainConditions seed) (hs : IncrementsOriginalSmoothInputs seed)
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
    (hQ₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ seed.parameterNormDomain b₀)
    (hs₀ : s₀ ∈ seed.parameterSet) (l : Fin seed.primaryCount) (j : ℕ) (ell : ℝ) :
    paperAtlasWeighted 0 j ell (actualOriginalTotalPhaseCoordinates (passiveOriginalData s₀ seed B Q) l)
      (incrementsOriginalPrimaryDifferentiation (passiveOriginalData s₀ seed B Q) l)
      (incrementsOriginalPrimaryEvaluation (passiveOriginalData s₀ seed B Q) l) ≤
    paperAtlasWeighted 0 j ell (actualOriginalTotalPhaseCoordinates seed l)
      (incrementsOriginalPrimaryDifferentiation seed l) (incrementsOriginalPrimaryEvaluation seed l) := by
  rw [paperAtlasWeighted_congr_on 0 j ell
    (incrementsOriginalPrimaryDifferentiation (passiveOriginalData s₀ seed B Q) l)
    (incrementsOriginalPrimaryEvaluation (passiveOriginalData s₀ seed B Q) l)
    (fun _ _ hy => ⟨hy.1.1,hy.2⟩)
    (passiveOriginal_totalPhase_rows s₀ seed B Q b₀ hd hs hb₀ (hd.parameter_subset hs₀) l)]
  calc
    _ ≤ paperAtlasWeighted 0 j ell
      (fun i : Fin seed.atlas.count × Fin B.count =>
        actualOriginalTotalPhaseCoordinates seed l (i.1,b₀) ∘ passiveOriginalSourceProjection (d := d))
      (incrementsOriginalPrimaryDifferentiation (passiveOriginalData s₀ seed B Q) l)
      (incrementsOriginalPrimaryEvaluation (passiveOriginalData s₀ seed B Q) l) := by
      unfold paperAtlasWeighted
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_right
      apply iSup_mono
      intro i
      exact passiveOriginal_selectRows_norm_le (a+0) (passiveOriginalCovectorSelect n d) _ _ _
    _ ≤ _ := passiveOriginal_primary_weighted_le s₀ seed B Q b₀ hb₀ hQ₀ hs₀
      hd.primary_open l 0 j ell (actualOriginalTotalPhaseCoordinates seed l)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_totalPhase_rows
#print axioms GlobalEmbedding.Continuation.passiveOriginal_totalPhase_weighted_le
