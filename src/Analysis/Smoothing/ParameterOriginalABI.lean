import Smoothing.IntegrationParameterModelJets
import Smoothing.ParameterOriginalNormAlgebra
import Smoothing.TensorParameterNorms

/-!
# Literal original map coordinates and anisotropic norms with parameters

The true product atlas and the original source-first ABI differ only by the
proved fixed coordinate and finite-index equivalences. The norm here is the
original spatial 0/1/2 partial packet followed by additional JOINT derivatives.
It is not identified with an isotropic total-C(j+2) norm when d is nonzero.
The parameter atlas B here is genuinely finite and covers P. This includes
compact parameter manifolds, but does not assert preparation of arbitrary
compact subsets of a larger parameter manifold with only local chart data.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Filter Set Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

section Reindex
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {n d q : ℕ}

/-- Reindex the genuine spatial packet without changing the original maximum. -/
theorem parameterSpatialCj_reindex (e : ι ≃ κ) (j : ℕ)
    (f : κ → (Fin (n+d) → ℝ) → Fin q → ℝ) (O S : κ → Set (Fin (n+d) → ℝ)) :
    parameterSpatialCj (n := n) (d := d) j (fun i => f (e i))
      (fun i => O (e i)) (fun i => S (e i)) = parameterSpatialCj (n := n) (d := d) j f O S :=
  paperAtlasCj_reindex (e.prodCongr (Equiv.refl (ParameterSpatialWord n))) j
    (parameterSpatialPacket (n := n) (d := d) f) (fun iw => O iw.1) (fun iw => S iw.1)

theorem parameterSpatialWeighted_reindex (e : ι ≃ κ) (m : ℕ) (t : ℝ)
    (f : κ → (Fin (n+d) → ℝ) → Fin q → ℝ) (O S : κ → Set (Fin (n+d) → ℝ)) :
    parameterSpatialWeighted (n := n) (d := d) m t (fun i => f (e i))
      (fun i => O (e i)) (fun i => S (e i)) = parameterSpatialWeighted (n := n) (d := d) m t f O S :=
  paperAtlasWeighted_reindex (e.prodCongr (Equiv.refl (ParameterSpatialWord n))) 0 m t
    (parameterSpatialPacket (n := n) (d := d) f) (fun iw => O iw.1) (fun iw => S iw.1)

theorem parameterSpatialCj_mono_evaluation (j : ℕ)
    (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ) (O S R : ι → Set (Fin (n+d) → ℝ))
    (hSR : ∀ i, S i ⊆ R i) :
    parameterSpatialCj (n := n) (d := d) j f O S ≤ parameterSpatialCj (n := n) (d := d) j f O R :=
  paperAtlasCj_mono_evaluation j (parameterSpatialPacket (n := n) (d := d) f)
    (fun iw => O iw.1) (fun iw => S iw.1) (fun iw => R iw.1) (fun iw => hSR iw.1)

theorem parameterSpatialWeighted_mono_evaluation (m : ℕ) (t : ℝ)
    (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ) (O S R : ι → Set (Fin (n+d) → ℝ))
    (hSR : ∀ i, S i ⊆ R i) :
    parameterSpatialWeighted (n := n) (d := d) m t f O S ≤ parameterSpatialWeighted (n := n) (d := d) m t f O R :=
  paperAtlasWeighted_mono_evaluation 0 m t (parameterSpatialPacket (n := n) (d := d) f)
    (fun iw => O iw.1) (fun iw => S iw.1) (fun iw => R iw.1) (fun iw => hSR iw.1)

end Reindex

variable {n d q : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance : ChartedSpace (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

variable (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
local notation "cp" => EuclideanSpace.equiv (Fin d) ℝ
local notation "cs" => EuclideanSpace.equiv (Fin n) ℝ
local notation "cy" => EuclideanSpace.equiv (Fin q) ℝ
local notation "AB" => parameterProductAtlas A B

/-- Values of the original native map agree literally in source-first coordinates. -/
theorem parameterBufferedModelCoordinates_eq_original
    (u : P × M → EuclideanSpace ℝ (Fin q)) (i : Fin A.count × Fin B.count)
    (y : Fin (n+d) → ℝ) :
    parameterBufferedModelCoordinates A B cp cs cy u (parameterTensorAtlasIndex A B i) y =
      incrementsOriginalMapCoordinates A B.chart u i y := by
  change cy (u (((AB).chart (parameterTensorAtlasIndex A B i)).symm
    ((parameterTensorModelEquiv n d).symm y))) = _
  rw [parameterTensorModel_jointPoint A B i y]
  rfl

/-- The original source-first differentiation domain is exactly preserved. -/
theorem parameterBufferedModelTargets_eq_original (i : Fin A.count × Fin B.count) :
    parameterBufferedModelTargets A B cp cs (parameterTensorAtlasIndex A B i) =
      incrementsOriginalDifferentiation A B.chart i := parameterTensorModel_targets A B i

/-- The original product inner evaluation domain is exactly preserved. -/
theorem parameterBufferedModelInner_eq_original (i : Fin A.count × Fin B.count) :
    parameterBufferedModelInner A B cp cs (parameterTensorAtlasIndex A B i) =
      parameterTensorOriginalInner A B i := parameterTensorModel_inner A B i

/-- Every true joint kernel-sampling point lies in the original independent
source and parameter buffers; those original input norms suffice. -/
theorem parameterBufferedModelSampling_subset_original (i : Fin A.count × Fin B.count) :
    parameterBufferedModelSampling A B cp cs (parameterTensorAtlasIndex A B i) ⊆
      parameterTensorOriginalSampling A B i := parameterTensorModel_sampling_subset A B i

/-- Original spatial-packet Cj equality on every true evaluation set. -/
theorem parameterMap_Cj_eq_original
    (u : P × M → EuclideanSpace ℝ (Fin q)) (j : ℕ)
    (S : Fin (B.count*A.count) → Set (Fin (n+d) → ℝ)) :
    parameterSpatialCj (n := n) (d := d) j (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) S =
    parameterSpatialCj (n := n) (d := d) j (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (fun i => S (parameterTensorAtlasIndex A B i)) := by
  erw [← parameterSpatialCj_reindex (parameterTensorAtlasIndex A B)]
  have hf : (fun i => parameterBufferedModelCoordinates A B cp cs cy u (parameterTensorAtlasIndex A B i)) =
      incrementsOriginalMapCoordinates A B.chart u := by
    funext i y
    exact parameterBufferedModelCoordinates_eq_original A B u i y
  have hO : (fun i => parameterBufferedModelTargets A B cp cs (parameterTensorAtlasIndex A B i)) =
      incrementsOriginalDifferentiation A B.chart := funext (parameterBufferedModelTargets_eq_original A B)
  rw [hf,hO]

/-- The same exact equality retains the original anisotropic weighted norm. -/
theorem parameterMap_weighted_eq_original
    (u : P × M → EuclideanSpace ℝ (Fin q)) (m : ℕ) (t : ℝ)
    (S : Fin (B.count*A.count) → Set (Fin (n+d) → ℝ)) :
    parameterSpatialWeighted (n := n) (d := d) m t (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) S =
    parameterSpatialWeighted (n := n) (d := d) m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (fun i => S (parameterTensorAtlasIndex A B i)) := by
  erw [← parameterSpatialWeighted_reindex (parameterTensorAtlasIndex A B)]
  have hf : (fun i => parameterBufferedModelCoordinates A B cp cs cy u (parameterTensorAtlasIndex A B i)) =
      incrementsOriginalMapCoordinates A B.chart u := by
    funext i y
    exact parameterBufferedModelCoordinates_eq_original A B u i y
  have hO : (fun i => parameterBufferedModelTargets A B cp cs (parameterTensorAtlasIndex A B i)) =
      incrementsOriginalDifferentiation A B.chart := funext (parameterBufferedModelTargets_eq_original A B)
  rw [hf,hO]

/-- Exact output norm on the original inner domains, without any chart-count loss. -/
theorem parameterMap_weighted_inner_eq_original
    (u : P × M → EuclideanSpace ℝ (Fin q)) (m : ℕ) (t : ℝ) :
    parameterSpatialWeighted (n := n) (d := d) m t (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelInner A B cp cs) =
    parameterSpatialWeighted (n := n) (d := d) m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalInner A B) := by
  erw [parameterMap_weighted_eq_original A B u m t]
  congr 1
  exact funext (parameterBufferedModelInner_eq_original A B)

/-- Source original Cj controls the smaller true sampling buffer norm. -/
theorem parameterMap_Cj_sampling_le_original
    (u : P × M → EuclideanSpace ℝ (Fin q)) (j : ℕ) :
    parameterSpatialCj (n := n) (d := d) j (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs) ≤
    parameterSpatialCj (n := n) (d := d) j (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) := by
  erw [parameterMap_Cj_eq_original A B u j]
  exact parameterSpatialCj_mono_evaluation _ _ _ _ _ (parameterBufferedModelSampling_subset_original A B)

/-- Source original weighted budgets control the genuine joint sampling norm. -/
theorem parameterMap_weighted_sampling_le_original
    (u : P × M → EuclideanSpace ℝ (Fin q)) (m : ℕ) (t : ℝ) :
    parameterSpatialWeighted (n := n) (d := d) m t (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs) ≤
    parameterSpatialWeighted (n := n) (d := d) m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) := by
  erw [parameterMap_weighted_eq_original A B u m t]
  exact parameterSpatialWeighted_mono_evaluation _ _ _ _ _ _ (parameterBufferedModelSampling_subset_original A B)

/-- Native smoothness of the actual map gives the original joint-coordinate regularity. -/
theorem parameterOriginalMapCoordinates_contDiffOn
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    {u : P × M → EuclideanSpace ℝ (Fin q)}
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ u) (i : Fin A.count × Fin B.count) :
    ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
      (incrementsOriginalDifferentiation A B.chart i) := by
  have h := parameterModelCoordinates_contDiffOn cp cs cy
    (parameterBufferedNativeCoordinates A B u) (fun j => ((AB).chart j).target)
    (parameterBufferedNativeCoordinates_contDiffOn A B hA hB hu) (parameterTensorAtlasIndex A B i)
  change ContDiffOn ℝ ∞ (parameterBufferedModelCoordinates A B cp cs cy u (parameterTensorAtlasIndex A B i))
    (parameterBufferedModelTargets A B cp cs (parameterTensorAtlasIndex A B i)) at h
  rw [parameterBufferedModelTargets_eq_original] at h
  apply h.congr
  intro y hy
  exact (parameterBufferedModelCoordinates_eq_original A B u i y).symm

/-- The paper's G-SG orientation equals SG-G in the literal original norm. -/
theorem parameterOriginalMap_weighted_sub_comm
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (u v : P × M → EuclideanSpace ℝ (Fin q))
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ v)
    (m : ℕ) (t : ℝ) (S : Fin A.count × Fin B.count → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i) :
    parameterSpatialWeighted (n := n) (d := d) m t
      (incrementsOriginalMapCoordinates A B.chart (fun z => u z-v z))
      (incrementsOriginalDifferentiation A B.chart) S =
    parameterSpatialWeighted (n := n) (d := d) m t
      (incrementsOriginalMapCoordinates A B.chart (fun z => v z-u z))
      (incrementsOriginalDifferentiation A B.chart) S := by
  have heq (u v : P × M → EuclideanSpace ℝ (Fin q)) :
      incrementsOriginalMapCoordinates A B.chart (fun z => u z-v z) =
      fun i y => incrementsOriginalMapCoordinates A B.chart u i y -
        incrementsOriginalMapCoordinates A B.chart v i y := by
    funext i y
    exact map_sub cy _ _
  rw [heq, heq]
  apply parameterSpatialWeighted_sub_comm m t _ _ _ S _ hSO
    (parameterOriginalMapCoordinates_contDiffOn A B hA hB hu)
    (parameterOriginalMapCoordinates_contDiffOn A B hA hB hv)
  intro i
  rw [← parameterBufferedModelTargets_eq_original A B i]
  exact (((AB).chart (parameterTensorAtlasIndex A B i)).open_target).preimage
    (parameterTensorModelEquiv n d).symm.continuous

#print axioms parameterOriginalMap_weighted_sub_comm
#print axioms parameterBufferedModelCoordinates_eq_original
#print axioms parameterMap_weighted_inner_eq_original
#print axioms parameterMap_weighted_sampling_le_original
end
end GlobalEmbedding.Continuation
