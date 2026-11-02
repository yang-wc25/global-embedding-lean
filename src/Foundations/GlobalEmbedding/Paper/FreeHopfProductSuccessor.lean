import GlobalEmbedding.Paper.FreeHopfProductNative
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The actual smooth successor decomposition of the Hopf product

Source: `literature/parallelizable-stable-plus-one/main.tex`, thm:free, lines430–495.
DAG node: `free-hopf-product-successor`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The dimensions of the actual old factors are the castSucc restriction of C. -/
abbrev freeHopfOldDimensions {m : ℕ} (C : Fin (m + 1) → ℕ) : Fin m → ℕ :=
  fun i ↦ C i.castSucc

/-- The literal old-factor/last-sphere decomposition, on the genuine original carrier. -/
def freeHopfProductSplit {m : ℕ} (C : Fin (m + 1) → ℕ) (x : FreeHopfProduct C) :
    FreeHopfProduct (freeHopfOldDimensions C) × PlanarHopfSphere (C (Fin.last m)) :=
  (fun i ↦ x i.castSucc, x (Fin.last m))

/-- The actual inverse is genuine dependent tuple snoc, preserving all factor types. -/
def freeHopfProductJoin {m : ℕ} (C : Fin (m + 1) → ℕ)
    (p : FreeHopfProduct (freeHopfOldDimensions C) ×
      PlanarHopfSphere (C (Fin.last m))) : FreeHopfProduct C := Fin.snoc p.1 p.2

/-- The genuine source carrier equivalence uses actual tuple restriction and snoc. -/
def freeHopfProductSplitEquiv {m : ℕ} (C : Fin (m + 1) → ℕ) :
    FreeHopfProduct C ≃
      FreeHopfProduct (freeHopfOldDimensions C) × PlanarHopfSphere (C (Fin.last m)) where
  toFun := freeHopfProductSplit C
  invFun := freeHopfProductJoin C
  left_inv x := Fin.snoc_init_self x
  right_inv p := by
    apply Prod.ext
    · funext i
      exact Fin.snoc_castSucc (α := fun i ↦ PlanarHopfSphere (C i)) p.2 p.1 i
    · exact Fin.snoc_last (α := fun i ↦ PlanarHopfSphere (C i)) p.2 p.1

/-- Literal source splitting is native smooth for the actual product sphere atlases. -/
theorem freeHopfProductSplit_contMDiff {m : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)] :
    ContMDiff (freeHopfModel C)
      ((freeHopfModel (freeHopfOldDimensions C)).prod (planarHopfModel (C (Fin.last m))))
      ∞ (freeHopfProductSplit C) := by
  have hold : ContMDiff (freeHopfModel C) (freeHopfModel (freeHopfOldDimensions C)) ∞
      (fun x : FreeHopfProduct C ↦ fun i : Fin m ↦ x i.castSucc) := by
    rw [show freeHopfModel (freeHopfOldDimensions C) =
      ModelWithCorners.pi (fun i ↦ planarHopfModel (C i.castSucc)) from
      (free_finite_product_model_eq _).symm]
    exact contMDiff_pi_iff.2 (fun i ↦ freeHopfProduct_contMDiff_apply C i.castSucc)
  exact hold.prodMk (freeHopfProduct_contMDiff_apply C (Fin.last m))

/-- Actual tuple snoc is native smooth, including the empty old product. -/
theorem freeHopfProductJoin_contMDiff {m : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)] :
    ContMDiff
      ((freeHopfModel (freeHopfOldDimensions C)).prod (planarHopfModel (C (Fin.last m))))
      (freeHopfModel C) ∞ (freeHopfProductJoin C) := by
  rw [show freeHopfModel C = ModelWithCorners.pi (fun i ↦ planarHopfModel (C i)) from
    (free_finite_product_model_eq _).symm]
  apply contMDiff_pi_iff.2
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [freeHopfProductJoin, Fin.snoc_last] using
      (contMDiff_snd : ContMDiff _ _ ∞
        (fun p : FreeHopfProduct (freeHopfOldDimensions C) ×
          PlanarHopfSphere (C (Fin.last m)) ↦ p.2))
  · simp only [freeHopfProductJoin, Fin.snoc_castSucc]
    convert! ((freeHopfProduct_contMDiff_apply (freeHopfOldDimensions C) j).comp
      contMDiff_fst) using 1

/-- An old actual Hopf factor flow splits into the same old flow and the fixed new sphere. -/
theorem freeHopfProductSplit_flow_old {m : ℕ} (C : Fin (m + 1) → ℕ)
    (i : Fin m) (t : ℝ) (x : FreeHopfProduct C) :
    freeHopfProductSplit C (freeHopfProductFlow C i.castSucc t x) =
      (freeHopfProductFlow (freeHopfOldDimensions C) i t (freeHopfProductSplit C x).1,
        (freeHopfProductSplit C x).2) := by
  apply Prod.ext
  · funext j
    simp only [freeHopfProductSplit, freeHopfProductFlow, freeHopfRealAction,
      Fin.castSucc_inj]
  · exact freeHopfProductFlow_apply_ne C i.castSucc (Fin.last m)
      (Fin.castSucc_ne_last i).symm t x

/-- The new actual Hopf flow is exactly the original single-sphere flow under splitting. -/
theorem freeHopfProductSplit_flow_last {m : ℕ} (C : Fin (m + 1) → ℕ)
    (t : ℝ) (x : FreeHopfProduct C) :
    freeHopfProductSplit C (freeHopfProductFlow C (Fin.last m) t x) =
      ((freeHopfProductSplit C x).1, planarHopfFlow t (freeHopfProductSplit C x).2) := by
  apply Prod.ext
  · funext j
    exact freeHopfProductFlow_apply_ne C (Fin.last m) j.castSucc
      (Fin.castSucc_ne_last j) t x
  · exact freeHopfProductFlow_apply C (Fin.last m) t x

/-- Joining an old flowed pair recovers exactly the original old-factor flow. -/
theorem freeHopfProductJoin_flow_old {m : ℕ} (C : Fin (m + 1) → ℕ)
    (i : Fin m) (t : ℝ)
    (p : FreeHopfProduct (freeHopfOldDimensions C) ×
      PlanarHopfSphere (C (Fin.last m))) :
    freeHopfProductJoin C (freeHopfProductFlow (freeHopfOldDimensions C) i t p.1, p.2) =
      freeHopfProductFlow C i.castSucc t (freeHopfProductJoin C p) := by
  apply (freeHopfProductSplitEquiv C).injective
  change freeHopfProductSplit C _ = freeHopfProductSplit C _
  rw [freeHopfProductSplit_flow_old]
  exact ((freeHopfProductSplitEquiv C).apply_symm_apply _).trans
    (congrArg (fun q ↦ (freeHopfProductFlow (freeHopfOldDimensions C) i t q.1, q.2))
      ((freeHopfProductSplitEquiv C).apply_symm_apply p)).symm

/-- Joining a new flowed pair recovers exactly the original last-factor flow. -/
theorem freeHopfProductJoin_flow_last {m : ℕ} (C : Fin (m + 1) → ℕ)
    (t : ℝ)
    (p : FreeHopfProduct (freeHopfOldDimensions C) ×
      PlanarHopfSphere (C (Fin.last m))) :
    freeHopfProductJoin C (p.1, planarHopfFlow t p.2) =
      freeHopfProductFlow C (Fin.last m) t (freeHopfProductJoin C p) := by
  apply (freeHopfProductSplitEquiv C).injective
  change freeHopfProductSplit C _ = freeHopfProductSplit C _
  rw [freeHopfProductSplit_flow_last]
  exact ((freeHopfProductSplitEquiv C).apply_symm_apply _).trans
    (congrArg (fun q ↦ (q.1, planarHopfFlow t q.2))
      ((freeHopfProductSplitEquiv C).apply_symm_apply p)).symm

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopfProductSplit_contMDiff
#print axioms GlobalEmbedding.Paper.freeHopfProductJoin_contMDiff
#print axioms GlobalEmbedding.Paper.freeHopfProductSplit_flow_old
#print axioms GlobalEmbedding.Paper.freeHopfProductJoin_flow_last
