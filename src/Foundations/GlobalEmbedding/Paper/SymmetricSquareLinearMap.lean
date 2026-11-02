import GlobalEmbedding.Paper.SymmetricBilinearDescend

namespace GlobalEmbedding.Paper

/-- The canonical algebraic symmetric-square map of an actual real linear map.
It descends the actual symmetric product after applying the linear map to both
arguments. Its symmetry proof is the existing named product symmetry theorem.
No norm or auxiliary metric occurs. Source: `defn:phase`, restriction to the
symmetric square of the actual covector kernel. -/
noncomputable def symmetricSquareLinearMap
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) : SymmetricSquare V →ₗ[ℝ] SymmetricSquare W :=
  symmetricBilinearDescend (((symmetricSquareProduct W).compl₂ f).comp f)
    (fun v w ↦ symmetricSquareProduct_comm W (f v) (f w))

end GlobalEmbedding.Paper
