import GlobalEmbedding.Paper.SymmetricSquareModuleTopology
import GlobalEmbedding.Paper.SymmetricBilinearDescendEvaluation

open scoped TensorProduct

namespace GlobalEmbedding.Paper

/-- An actual linear equivalence induces a continuous linear equivalence of the
existing exact binary quotients with their canonical real module topologies.

Proof: descend the symmetric bilinear products (v,w)↦[e(v)⊗e(w)] and the analogous
products for e⁻¹ using the already proved canonical descent. Their composites are
identity on every quotient product, hence on the whole quotient by tensor/quotient
extensionality. Every linear map from a canonical module topology to a topological
module is continuous, so both inverse directions are continuous. No norms are chosen.
Source: actual tangent-induced symmetric-square bundle charts in `defn:phase`. -/
theorem exists_symmetric_square_linear_equivalence
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : V ≃ₗ[ℝ] W) :
    letI := symmetricSquareModuleTopology V
    letI := symmetricSquareModuleTopology W
    ∃ e₂ : SymmetricSquare V ≃L[ℝ] SymmetricSquare W,
      ∀ v w, e₂ (symmetricSquareProduct V v w) = symmetricSquareProduct W (e v) (e w) := by
  let := symmetricSquareModuleTopology V
  let := symmetricSquareModuleTopology W
  have : ContinuousAdd (SymmetricSquare V) :=
    IsModuleTopology.toContinuousAdd ℝ (SymmetricSquare V)
  have : ContinuousAdd (SymmetricSquare W) :=
    IsModuleTopology.toContinuousAdd ℝ (SymmetricSquare W)
  let β : V →ₗ[ℝ] V →ₗ[ℝ] SymmetricSquare W :=
    { toFun := fun v ↦ (symmetricSquareProduct W (e v)).comp e.toLinearMap
      map_add' := fun u v ↦ by ext w; simp
      map_smul' := fun c v ↦ by ext w; simp }
  let γ : W →ₗ[ℝ] W →ₗ[ℝ] SymmetricSquare V :=
    { toFun := fun v ↦ (symmetricSquareProduct V (e.symm v)).comp e.symm.toLinearMap
      map_add' := fun u v ↦ by ext w; simp
      map_smul' := fun c v ↦ by ext w; simp }
  have hβ (v w : V) : β v w = β w v := symmetricSquareProduct_comm W _ _
  have hγ (v w : W) : γ v w = γ w v := symmetricSquareProduct_comm V _ _
  let f := symmetricBilinearDescend β hβ
  let g := symmetricBilinearDescend γ hγ
  have hf (v w : V) : f (symmetricSquareProduct V v w) =
      symmetricSquareProduct W (e v) (e w) := symmetricBilinearDescend_product β hβ v w
  have hg (v w : W) : g (symmetricSquareProduct W v w) =
      symmetricSquareProduct V (e.symm v) (e.symm w) :=
    symmetricBilinearDescend_product γ hγ v w
  have hgf : g.comp f = LinearMap.id := by
    apply (symmetricSquareRelations V).linearMap_qext
    apply TensorProduct.ext'
    intro v w
    change g (f (symmetricSquareProduct V v w)) = symmetricSquareProduct V v w
    rw [hf, hg]
    simp
  have hfg : f.comp g = LinearMap.id := by
    apply (symmetricSquareRelations W).linearMap_qext
    apply TensorProduct.ext'
    intro v w
    change f (g (symmetricSquareProduct W v w)) = symmetricSquareProduct W v w
    rw [hg, hf]
    simp
  let e₂ : SymmetricSquare V ≃L[ℝ] SymmetricSquare W :=
    { f with
      invFun := g
      left_inv := fun q ↦ congrArg (fun L : SymmetricSquare V →ₗ[ℝ] SymmetricSquare V ↦ L q) hgf
      right_inv := fun q ↦ congrArg (fun L : SymmetricSquare W →ₗ[ℝ] SymmetricSquare W ↦ L q) hfg
      continuous_toFun := IsModuleTopology.continuous_of_linearMap f
      continuous_invFun := IsModuleTopology.continuous_of_linearMap g }
  exact ⟨e₂, hf⟩

end GlobalEmbedding.Paper
