import FaithfulCollars.UniformManifoldRepairSupply
import Repair.ReferenceOriginalLocalFactory

/-!
# Literal original norms under the manufactured chart-count identities

Only finite index names change.  Every source/parameter chart, map,
tensor, differentiation domain and original norm set is kept.  The atlas
MAX is transported through an explicit equivalence of finite indices.
No estimate or replacement norm occurs in these equalities.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

theorem paperAtlasCj_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n q : ℕ} (e : ι ≃ κ) (j : ℕ)
    (f : κ → (Fin n → ℝ) → Fin q → ℝ) (O S : κ → Set (Fin n → ℝ)) :
    paperAtlasCj j (fun i => f (e i)) (fun i => O (e i)) (fun i => S (e i)) =
      paperAtlasCj j f O S := by
  unfold paperAtlasCj
  exact e.iSup_comp (g := fun i => paperCoordinateCj j (f i) (O i) (S i))

variable {n d N c c' : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

variable (A A' : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
  (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d))) (B' : Fin c' → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
  (hs : A'.count = A.count) (hp : c' = c)
  (hS : ∀ i, A'.chart i = A.chart (Fin.cast hs i))
  (hP : ∀ i, B' i = B (Fin.cast hp i))

def originalChartIndexEquiv : (Fin A'.count × Fin c') ≃ (Fin A.count × Fin c) :=
  Equiv.prodCongr (finCongr hs) (finCongr hp)

include hS hP

theorem originalJointPoint_cast (i : Fin A'.count × Fin c') (y : Fin (n+d) → ℝ) :
    incrementsOriginalJointPoint A' B' i y =
      incrementsOriginalJointPoint A B (Fin.cast hs i.1, Fin.cast hp i.2) y := by
  unfold incrementsOriginalJointPoint
  rw [hP i.2, hS i.1]

theorem originalDifferentiation_cast (i : Fin A'.count × Fin c') :
    incrementsOriginalDifferentiation A' B' i =
      incrementsOriginalDifferentiation A B (Fin.cast hs i.1, Fin.cast hp i.2) := by
  unfold incrementsOriginalDifferentiation
  rw [hP i.2, hS i.1]

theorem originalEvaluation_cast
    (Omega : Fin A.count → Set (EuclideanSpace ℝ (Fin n))) (Q : Fin c → Set (EuclideanSpace ℝ (Fin d))) (K : Set P)
    (i : Fin A'.count × Fin c') :
    incrementsOriginalEvaluation A' B' (fun i => Omega (Fin.cast hs i))
      (fun i => Q (Fin.cast hp i)) K i =
    incrementsOriginalEvaluation A B Omega Q K (Fin.cast hs i.1, Fin.cast hp i.2) := by
  unfold incrementsOriginalEvaluation incrementsOriginalDifferentiation incrementsOriginalJointPoint
  rw [hP i.2, hS i.1]

theorem originalMapCoordinates_cast
    (f : P × M → EuclideanSpace ℝ (Fin N)) (i : Fin A'.count × Fin c') :
    incrementsOriginalMapCoordinates A' B' f i =
      incrementsOriginalMapCoordinates A B f (Fin.cast hs i.1, Fin.cast hp i.2) := by
  funext y
  unfold incrementsOriginalMapCoordinates
  rw [originalJointPoint_cast A A' B B' hs hp hS hP i y]

theorem originalTensorCoordinates_cast
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x))
    (i : Fin A'.count × Fin c') :
    incrementsOriginalTensorCoordinates A' B' T i =
      incrementsOriginalTensorCoordinates A B T (Fin.cast hs i.1, Fin.cast hp i.2) := by
  funext y k
  unfold incrementsOriginalTensorCoordinates incrementsOriginalJointPoint incrementsOriginalSourceVector
  rw [hP i.2, hS i.1]

theorem originalMapCj_cast
    (Omega : Fin A.count → Set (EuclideanSpace ℝ (Fin n))) (Q : Fin c → Set (EuclideanSpace ℝ (Fin d))) (K : Set P)
    (f : P × M → EuclideanSpace ℝ (Fin N)) (j : ℕ) :
    paperAtlasCj j (incrementsOriginalMapCoordinates A' B' f)
      (incrementsOriginalDifferentiation A' B')
      (incrementsOriginalEvaluation A' B' (fun i => Omega (Fin.cast hs i))
        (fun i => Q (Fin.cast hp i)) K) =
    paperAtlasCj j (incrementsOriginalMapCoordinates A B f)
      (incrementsOriginalDifferentiation A B) (incrementsOriginalEvaluation A B Omega Q K) := by
  calc
    _ = paperAtlasCj j
        (fun i => incrementsOriginalMapCoordinates A B f (originalChartIndexEquiv A A' hs hp i))
        (fun i => incrementsOriginalDifferentiation A B (originalChartIndexEquiv A A' hs hp i))
        (fun i => incrementsOriginalEvaluation A B Omega Q K (originalChartIndexEquiv A A' hs hp i)) := by
      congr 1
      · funext i
        exact originalMapCoordinates_cast A A' B B' hs hp hS hP f i
      · funext i
        exact originalDifferentiation_cast A A' B B' hs hp hS hP i
      · funext i
        exact originalEvaluation_cast A A' B B' hs hp hS hP Omega Q K i
    _ = _ := paperAtlasCj_equiv (originalChartIndexEquiv A A' hs hp) j _ _ _

theorem originalTensorCj_cast
    (Omega : Fin A.count → Set (EuclideanSpace ℝ (Fin n))) (Q : Fin c → Set (EuclideanSpace ℝ (Fin d))) (K : Set P)
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)) (j : ℕ) :
    paperAtlasCj j (incrementsOriginalTensorCoordinates A' B' T)
      (incrementsOriginalDifferentiation A' B')
      (incrementsOriginalEvaluation A' B' (fun i => Omega (Fin.cast hs i))
        (fun i => Q (Fin.cast hp i)) K) =
    paperAtlasCj j (incrementsOriginalTensorCoordinates A B T)
      (incrementsOriginalDifferentiation A B) (incrementsOriginalEvaluation A B Omega Q K) := by
  calc
    _ = paperAtlasCj j
        (fun i => incrementsOriginalTensorCoordinates A B T (originalChartIndexEquiv A A' hs hp i))
        (fun i => incrementsOriginalDifferentiation A B (originalChartIndexEquiv A A' hs hp i))
        (fun i => incrementsOriginalEvaluation A B Omega Q K (originalChartIndexEquiv A A' hs hp i)) := by
      congr 1
      · funext i
        exact originalTensorCoordinates_cast A A' B B' hs hp hS hP T i
      · funext i
        exact originalDifferentiation_cast A A' B B' hs hp hS hP i
      · funext i
        exact originalEvaluation_cast A A' B B' hs hp hS hP Omega Q K i
    _ = _ := paperAtlasCj_equiv (originalChartIndexEquiv A A' hs hp) j _ _ _

/-- Internal compact carriers embed in the full original evaluation set,
with the original parameter set retained. -/
theorem internalEvaluation_subset_original
    (Omega : Fin A.count → Set (EuclideanSpace ℝ (Fin n))) (Q : Fin c → Set (EuclideanSpace ℝ (Fin d)))
    (CS : Fin A'.count → Set (EuclideanSpace ℝ (Fin n))) (CP : Fin c' → Set (EuclideanSpace ℝ (Fin d))) (K : Set P)
    (hCS : ∀ i, CS i ⊆ Omega (Fin.cast hs i))
    (hCP : ∀ i, CP i ⊆ Q (Fin.cast hp i)) (i : Fin A'.count × Fin c') :
    incrementsOriginalEvaluation A' B' CS CP K i ⊆
      incrementsOriginalEvaluation A B Omega Q K (Fin.cast hs i.1, Fin.cast hp i.2) := by
  rw [← originalEvaluation_cast A A' B B' hs hp hS hP Omega Q K i]
  intro y hy
  exact ⟨hy.1, hCS i.1 hy.2.1, hCP i.2 hy.2.2.1, hy.2.2.2⟩

end GlobalEmbedding.Continuation.FaithfulCollars

#print axioms GlobalEmbedding.Continuation.FaithfulCollars.originalMapCj_cast
#print axioms GlobalEmbedding.Continuation.FaithfulCollars.originalTensorCj_cast
#print axioms GlobalEmbedding.Continuation.FaithfulCollars.internalEvaluation_subset_original
