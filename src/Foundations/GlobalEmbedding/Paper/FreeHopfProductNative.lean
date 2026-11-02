import GlobalEmbedding.Paper.FreeFiniteProductManifold
import GlobalEmbedding.Paper.PlanarHopfFlow

/-!
# The genuine finite Hopf product and commuting period-one flows

Source: `literature/parallelizable-stable-plus-one/main.tex`, setup:partial, lines216–232.
DAG node: `free-hopf-product-native`.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The actual whole product of the paper's unit complex spheres. -/
abbrev FreeHopfProduct {a : ℕ} (C : Fin a → ℕ) := ∀ i, PlanarHopfSphere (C i)

/-- The ordinary real vector model of the genuine finite sphere product atlas. -/
abbrev FreeHopfModelSpace {a : ℕ} (C : Fin a → ℕ) :=
  ∀ i, EuclideanSpace ℝ (Fin (2 * C i - 1))

/-- Its identity model with corners, preserving all native product coordinates. -/
abbrev freeHopfModel {a : ℕ} (C : Fin a → ℕ) := 𝓘(ℝ, FreeHopfModelSpace C)

instance freeHopfProductChartedSpace {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] : ChartedSpace (FreeHopfModelSpace C) (FreeHopfProduct C) :=
  freeFiniteProductChartedSpace (fun i ↦ EuclideanSpace ℝ (Fin (2 * C i - 1)))
    (fun i ↦ PlanarHopfSphere (C i))

/-- Native product-atlas compatibility follows from the actual factor sphere manifolds. -/
instance freeHopfProduct_isManifold {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] : IsManifold (freeHopfModel C) ∞ (FreeHopfProduct C) :=
  free_finite_product_isManifold _ _ ∞

/-- Actual sphere compactness gives compactness of the whole product, including a=0. -/
theorem freeHopfProduct_compact {a : ℕ} (C : Fin a → ℕ) :
    CompactSpace (FreeHopfProduct C) := inferInstance

/-- An actual factor projection is native smooth in the ordinary product model. -/
theorem freeHopfProduct_contMDiff_apply {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (i : Fin a) :
    ContMDiff (freeHopfModel C) (planarHopfModel (C i)) ∞
      (fun x : FreeHopfProduct C ↦ x i) := by
  rw [show freeHopfModel C = ModelWithCorners.pi (fun i ↦ planarHopfModel (C i)) from
    (free_finite_product_model_eq _).symm]
  exact contMDiff_apply

/-- The literal simultaneous real Hopf action, using the original period-one factors. -/
def freeHopfRealAction {a : ℕ} (C : Fin a → ℕ) (t : Fin a → ℝ)
    (x : FreeHopfProduct C) : FreeHopfProduct C := fun i ↦ planarHopfFlow (t i) (x i)

@[simp] theorem freeHopfRealAction_zero {a : ℕ} (C : Fin a → ℕ)
    (x : FreeHopfProduct C) : freeHopfRealAction C 0 x = x := by
  funext i
  exact planarHopfFlow_zero (x i)

/-- The literal real action law, without choosing any orbit origin. -/
theorem freeHopfRealAction_add {a : ℕ} (C : Fin a → ℕ) (s t : Fin a → ℝ)
    (x : FreeHopfProduct C) :
    freeHopfRealAction C (s + t) x = freeHopfRealAction C s (freeHopfRealAction C t x) := by
  funext i
  exact planarHopfFlow_add (s i) (t i) (x i)

/-- Joint native smoothness comes from the genuine single-factor action and projections. -/
theorem freeHopfRealAction_contMDiff {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] :
    ContMDiff (𝓘(ℝ, Fin a → ℝ).prod (freeHopfModel C)) (freeHopfModel C) ∞
      (fun p : (Fin a → ℝ) × FreeHopfProduct C ↦ freeHopfRealAction C p.1 p.2) := by
  rw [show freeHopfModel C = ModelWithCorners.pi (fun i ↦ planarHopfModel (C i)) from
    (free_finite_product_model_eq _).symm]
  apply contMDiff_pi_iff.2
  intro i
  exact (planarHopfFlow_contMDiff (C i)).comp
    (((contDiff_apply ℝ (fun _ : Fin a ↦ ℝ) i).contMDiff.comp contMDiff_fst).prodMk
      (contMDiff_apply.comp contMDiff_snd))

/-- The i-th real factor flow leaves every other factor fixed. -/
def freeHopfProductFlow {a : ℕ} (C : Fin a → ℕ) (i : Fin a) (t : ℝ)
    (x : FreeHopfProduct C) : FreeHopfProduct C :=
  freeHopfRealAction C (fun j ↦ if j = i then t else 0) x

/-- The original partial derivative is the actual derivative along the i-th Hopf orbit. -/
def freeHopfDeriv {a : ℕ} (C : Fin a → ℕ) (i : Fin a)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : FreeHopfProduct C → F) (x : FreeHopfProduct C) : F :=
  orbitDeriv (freeHopfProductFlow C i) f x

@[simp] theorem freeHopfProductFlow_apply {a : ℕ} (C : Fin a → ℕ)
    (i : Fin a) (t : ℝ) (x : FreeHopfProduct C) :
    freeHopfProductFlow C i t x i = planarHopfFlow t (x i) := by
  simp [freeHopfProductFlow, freeHopfRealAction]

/-- The unchanged factor identity is literal, with no heterogeneous tangent transport. -/
theorem freeHopfProductFlow_apply_ne {a : ℕ} (C : Fin a → ℕ)
    (i j : Fin a) (hji : j ≠ i) (t : ℝ) (x : FreeHopfProduct C) :
    freeHopfProductFlow C i t x j = x j := by
  simp [freeHopfProductFlow, freeHopfRealAction, hji]

@[simp] theorem freeHopfProductFlow_zero {a : ℕ} (C : Fin a → ℕ)
    (i : Fin a) (x : FreeHopfProduct C) : freeHopfProductFlow C i 0 x = x := by
  funext j
  simp [freeHopfProductFlow, freeHopfRealAction]

/-- The actual factor flow has the original additive time law. -/
theorem freeHopfProductFlow_add {a : ℕ} (C : Fin a → ℕ)
    (i : Fin a) (s t : ℝ) (x : FreeHopfProduct C) :
    freeHopfProductFlow C i (s + t) x =
      freeHopfProductFlow C i s (freeHopfProductFlow C i t x) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [freeHopfProductFlow_apply, planarHopfFlow_add]
  · simp [freeHopfProductFlow_apply_ne, hji]

@[simp] theorem freeHopfProductFlow_one {a : ℕ} (C : Fin a → ℕ)
    (i : Fin a) (x : FreeHopfProduct C) : freeHopfProductFlow C i 1 x = x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · exact freeHopfProductFlow_apply_ne C i j hji 1 x

/-- All genuine factor flows commute, including the same-factor case. -/
theorem freeHopfProductFlow_commute {a : ℕ} (C : Fin a → ℕ)
    (i j : Fin a) (s t : ℝ) (x : FreeHopfProduct C) :
    freeHopfProductFlow C i s (freeHopfProductFlow C j t x) =
      freeHopfProductFlow C j t (freeHopfProductFlow C i s x) := by
  funext k
  simp only [freeHopfProductFlow, freeHopfRealAction]
  rw [← planarHopfFlow_add, ← planarHopfFlow_add, add_comm]

/-- Joint native smoothness of each literal period-one factor flow. -/
theorem freeHopfProductFlow_contMDiff {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (i : Fin a) :
    ContMDiff (𝓘(ℝ, ℝ).prod (freeHopfModel C)) (freeHopfModel C) ∞
      (fun p : ℝ × FreeHopfProduct C ↦ freeHopfProductFlow C i p.1 p.2) := by
  rw [show freeHopfModel C = ModelWithCorners.pi (fun j ↦ planarHopfModel (C j)) from
    (free_finite_product_model_eq _).symm]
  apply contMDiff_pi_iff.2
  intro j
  by_cases hji : j = i
  · subst j
    simp only [freeHopfProductFlow_apply]
    exact (planarHopfFlow_contMDiff (C i)).comp
      (contMDiff_fst.prodMk (contMDiff_apply.comp contMDiff_snd))
  · have he : (fun p : ℝ × FreeHopfProduct C ↦ freeHopfProductFlow C i p.1 p.2 j) =
        (fun p : ℝ × FreeHopfProduct C ↦ p.2 j) := by
      funext p
      exact freeHopfProductFlow_apply_ne C i j hji p.1 p.2
    rw [he]
    exact contMDiff_apply.comp contMDiff_snd

/-- The proved actual product flow supplies the shared period-one smooth-flow API. -/
def freeHopfProductSmoothFlow {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (i : Fin a) :
    PeriodOneSmoothFlow (freeHopfModel C) (FreeHopfProduct C) where
  flow := freeHopfProductFlow C i
  flow_zero := freeHopfProductFlow_zero C i
  flow_add := freeHopfProductFlow_add C i
  flow_one := freeHopfProductFlow_one C i
  smooth := freeHopfProductFlow_contMDiff C i

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopfProduct_isManifold
#print axioms GlobalEmbedding.Paper.freeHopfRealAction_contMDiff
#print axioms GlobalEmbedding.Paper.freeHopfProductFlow_commute
#print axioms GlobalEmbedding.Paper.freeHopfProductSmoothFlow
