import Smoothing.TensorParameterFrames
import Smoothing.TensorModelCoordinates
import Smoothing.IntegrationSpatialCoordinates

/-!
# Exact original source-first coordinate ABI for parameterized tensors

The actual joint model is parameter × source. Its fixed continuous linear
coordinate presentation uses source coordinates first, exactly as the original
native tensor ABI. A finite index equivalence retains the same actual charts.
No Euclidean/Pi operator-norm isometry is asserted or required.
-/

open Module Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Continuation Function Set
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Offline

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Actual Euclidean product model to the original source-first coordinate vector. -/
def parameterTensorModelEquiv (n d : ℕ) :
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] (Fin (n + d) → ℝ) :=
  ((EuclideanSpace.equiv (Fin d) ℝ).prodCongr (EuclideanSpace.equiv (Fin n) ℝ)).trans
    (sourceFirstCoordinates n d)

@[simp] theorem parameterTensorModelEquiv_symm_apply {n d : ℕ} (y : Fin (n + d) → ℝ) :
    (parameterTensorModelEquiv n d).symm y =
      (incrementsOriginalParameterPoint y, incrementsOriginalSourcePoint y) := rfl

variable {n d : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

/-- The SAME finite chart family indexed in the original source-first order. -/
def parameterTensorAtlasIndex
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) :
    (Fin A.count × Fin B.count) ≃ Fin (parameterProductAtlas A B).count :=
  (Equiv.prodComm _ _).trans finProdFinEquiv

@[simp] theorem parameterTensorAtlasIndex_apply
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (i : Fin A.count × Fin B.count) :
    parameterTensorAtlasIndex A B i = finProdFinEquiv (i.2, i.1) := rfl

/-- The inverse product chart is literally the original native joint point. -/
theorem parameterTensorModel_jointPoint
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (i : Fin A.count × Fin B.count) (y : Fin (n + d) → ℝ) :
    ((parameterProductAtlas A B).chart (parameterTensorAtlasIndex A B i)).symm
      ((parameterTensorModelEquiv n d).symm y) =
        incrementsOriginalJointPoint A B.chart i y := by
  simp only [parameterTensorAtlasIndex, Equiv.trans_apply, Equiv.prodComm_apply, parameterProductAtlas, parameterProductIndex,
    Equiv.symm_apply_apply, parameterTensorModelEquiv_symm_apply]
  rfl

/-- The actual open differentiation domain is exactly the original one. -/
theorem parameterTensorModel_targets
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (i : Fin A.count × Fin B.count) :
    bufferedModelTargets (parameterProductAtlas A B) (parameterTensorModelEquiv n d)
      (parameterTensorAtlasIndex A B i) = incrementsOriginalDifferentiation A B.chart i := by
  ext y
  change ((parameterTensorModelEquiv n d).symm y) ∈
    ((parameterProductAtlas A B).chart (parameterTensorAtlasIndex A B i)).target ↔ _
  simp only [parameterTensorModelEquiv_symm_apply, parameterTensorAtlasIndex, Equiv.trans_apply, Equiv.prodComm_apply,
    parameterProductAtlas, parameterProductIndex, Equiv.symm_apply_apply]
  exact and_comm

/-- Every original ordered coefficient is exactly that of the same native
parameterized tensor in the same actual source tangent basis. -/
theorem parameterTensorModelCoordinates_eq_original
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (i : Fin A.count × Fin B.count) (y : Fin (n + d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B.chart i) :
    bufferedTensorModelCoordinates (parameterProductAtlas A B) (parameterTensorModelEquiv n d)
      (parameterTensorNativeFrame A B hA) (fun z => H z.1 z.2)
      (parameterTensorAtlasIndex A B i) y = incrementsOriginalTensorCoordinates A B.chart H i y := by
  rw [incrementsOriginalTensorCoordinates_eq_nativeFrame A hA B.chart H i y hy]
  simp only [bufferedTensorModelCoordinates, modelCoordinateFamily, bufferedTensorNativeCoordinates,
    Function.comp_apply, tensorCoefficientField, parameterTensorNativeFrame,
    parameterTensorAtlasIndex_apply, parameterProductIndex, Equiv.symm_apply_apply]
  rw [← parameterTensorAtlasIndex_apply, parameterTensorModel_jointPoint]

/-- Reindexing the SAME family does not change the original chart maximum. -/
theorem paperAtlasCj_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] {s q : ℕ}
    (e : ι ≃ κ) (j : ℕ) (f : κ → (Fin s → ℝ) → Fin q → ℝ)
    (O S : κ → Set (Fin s → ℝ)) :
    paperAtlasCj j (fun i => f (e i)) (fun i => O (e i)) (fun i => S (e i)) =
      paperAtlasCj j f O S := by
  unfold paperAtlasCj
  exact e.iSup_comp (g := fun k => paperCoordinateCj j (f k) (O k) (S k))

theorem paperAtlasWeighted_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] {s q : ℕ}
    (e : ι ≃ κ) (base m : ℕ) (t : ℝ) (f : κ → (Fin s → ℝ) → Fin q → ℝ)
    (O S : κ → Set (Fin s → ℝ)) :
    paperAtlasWeighted base m t (fun i => f (e i)) (fun i => O (e i)) (fun i => S (e i)) =
      paperAtlasWeighted base m t f O S := by
  unfold paperAtlasWeighted
  apply Finset.sum_congr rfl
  intro j _
  rw [paperAtlasCj_reindex]

end

end GlobalEmbedding.Offline
