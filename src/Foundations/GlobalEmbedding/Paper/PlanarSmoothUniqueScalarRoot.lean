import GlobalEmbedding.Paper.BalancedImplicitLocalSolution
import Mathlib.Order.Hom.Set

/-!
# Smoothness of the genuine scalar root on an open parameter domain

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, line261.
The root is the actual scalar order-isomorphism inverse, not supplied solution data.
-/

open Set Filter
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- The actual unique scalar zero is C∞ on the original open parameter domain.
Local existence/smoothness comes from the already proved implicit solution theorem;
strict monotonicity identifies those local solutions with the actual chosen root. -/
theorem planar_scalar_root_contDiffOn
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    (U : Set P) (hU : IsOpen U) (f : P → ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ (fun p : P × ℝ ↦ f p.1 p.2) (U ×ˢ univ))
    (hm : ∀ p, StrictMono (f p)) (hs : ∀ p, Function.Surjective (f p))
    (hd : ∀ p ∈ U, ∀ t, deriv (f p) t ≠ 0) :
    ContDiffOn ℝ ∞ (fun p ↦ (StrictMono.orderIsoOfSurjective (f p) (hm p) (hs p)).symm 0) U := by
  let root (p : P) := (StrictMono.orderIsoOfSurjective (f p) (hm p) (hs p)).symm 0
  have hr (p : P) : f p (root p) = 0 :=
    (StrictMono.orderIsoOfSurjective (f p) (hm p) (hs p)).apply_symm_apply 0
  intro p hp
  have hAt : ContDiffAt ℝ ∞ (fun q : P × ℝ ↦ f q.1 q.2) (p, root p) :=
    hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)
  have hslice : HasFDerivAt (f p)
      ((fderiv ℝ (fun q : P × ℝ ↦ f q.1 q.2) (p, root p)).comp
        (ContinuousLinearMap.inr ℝ P ℝ)) (root p) :=
    (hAt.differentiableAt (by simp)).hasFDerivAt.comp (root p)
      (hasFDerivAt_prodMk_right p (root p))
  have hscalar := hslice.differentiableAt.hasDerivAt
  have hi : (fderiv ℝ (fun q : P × ℝ ↦ f q.1 q.2) (p, root p) ∘L
      ContinuousLinearMap.inr ℝ P ℝ).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ (hd p hp (root p))), ?_⟩
    rw [hslice.unique hscalar.hasFDerivAt]
    apply ContinuousLinearMap.ext
    intro r
    exact rfl
  obtain ⟨V, hV, hpV, _, w, hw, _, hwf⟩ := balanced_implicit_local_solution U hU
    (fun q : P × ℝ ↦ f q.1 q.2) hf p (root p) hp (hr p) hi
  have heq : root =ᶠ[𝓝 p] w := by
    filter_upwards [hV.mem_nhds hpV] with q hq
    exact (hm q).injective ((hr q).trans (hwf q hq).symm)
  exact ((hw.contDiffAt (hV.mem_nhds hpV)).congr_of_eventuallyEq heq).contDiffWithinAt

#print axioms planar_scalar_root_contDiffOn

end GlobalEmbedding.Paper
