import GlobalEmbedding.Paper.CovectorKernelTrial
import GlobalEmbedding.Paper.CovectorRestrictionBound
import Mathlib.Topology.Semicontinuity.Basic

open scoped TensorProduct
open Filter Topology

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance uscSquareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance uscSquareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- The actual restricted minimum singular norm is upper semicontinuous at
every nonzero covector. Proof: choose an actual unit minimizing vector at the
base covector and move it by the actual kernel projection. Its ambient norm
remains positive nearby. The continuous norm ratio is an upper bound for the
nearby minima and equals the minimum at the base point. Source: `defn:phase`.
-/
theorem covector_upper_semicontinuity
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hdim : 2 ≤ Module.finrank ℝ E) (S : SymmetricSquare E →L[ℝ] F)
    (ξ0 : E →L[ℝ] ℝ) (hξ0 : ξ0 ≠ 0) :
    UpperSemicontinuousAt
      (fun ξ : E →L[ℝ] ℝ ↦ leastSingularNorm (E := SymmetricSquare ξ.ker) (F := F)
        (covectorRestriction S ξ)) ξ0 := by
  obtain ⟨v, hv⟩ : ∃ v : E, ξ0 v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hξ0
    ext v
    exact hn v
  have : Nontrivial ξ0.ker := covector_kernel_nontrivial hdim ξ0
  have : Nontrivial (SymmetricSquare ξ0.ker) := symmetric_square_nontrivial
  obtain ⟨z0, hz0, hmin⟩ :=
    (least_singular_norm_attainment (E := SymmetricSquare ξ0.ker) (F := F)
      (covectorRestriction S ξ0)).1
  let a := fun ξ : E →L[ℝ] ℝ ↦ symmetricSquareMapL (covectorKernelProjection v ξ)
    (symmetricSquareMapL ξ0.ker.subtypeL z0)
  have htrial := covector_kernel_trial v ξ0 hv z0
  have ha : ContinuousAt a ξ0 := htrial.1
  have ha0 : a ξ0 = symmetricSquareMapL ξ0.ker.subtypeL z0 := htrial.2.1
  have hnorm : ‖a ξ0‖ = 1 := by
    rw [ha0, symmetric_square_subspace_isometry ξ0.ker z0, hz0]
  let r := fun ξ : E →L[ℝ] ℝ ↦ ‖S (a ξ)‖ / ‖a ξ‖
  have hr : ContinuousAt r ξ0 :=
    (S.continuous.continuousAt.comp ha).norm.div ha.norm (by rw [hnorm]; norm_num)
  have hr0 : r ξ0 = leastSingularNorm (E := SymmetricSquare ξ0.ker) (F := F)
      (covectorRestriction S ξ0) := by
    change ‖S (a ξ0)‖ / ‖a ξ0‖ = _
    rw [hnorm, div_one, ha0]
    exact hmin
  intro t ht
  have hrt : ∀ᶠ ξ in 𝓝 ξ0, r ξ < t := hr (gt_mem_nhds (by rwa [hr0]))
  have hvnear : ∀ᶠ ξ : E →L[ℝ] ℝ in 𝓝 ξ0, ξ v ≠ 0 :=
    (continuous_id.clm_apply continuous_const).continuousAt.eventually_ne hv
  have hanear : ∀ᶠ ξ in 𝓝 ξ0, 0 < ‖a ξ‖ := ha.norm (lt_mem_nhds (by change 0 < ‖a ξ0‖; rw [hnorm]; norm_num))
  filter_upwards [hrt, hvnear, hanear] with ξ hrt hξ hpos
  obtain ⟨z, hz, hznorm⟩ := htrial.2.2 ξ hξ
  have : Nontrivial ξ.ker := covector_kernel_nontrivial hdim ξ
  have : Nontrivial (SymmetricSquare ξ.ker) := symmetric_square_nontrivial
  have he := (least_singular_norm_bound (E := SymmetricSquare ξ.ker) (F := F)
    (covectorRestriction S ξ)).2.1 z
  change leastSingularNorm (E := SymmetricSquare ξ.ker) (F := F)
    (covectorRestriction S ξ) * ‖z‖ ≤ ‖S (symmetricSquareMapL ξ.ker.subtypeL z)‖ at he
  rw [hz, hznorm] at he
  exact lt_of_le_of_lt ((le_div_iff₀ hpos).mpr he) hrt

end GlobalEmbedding.Paper
