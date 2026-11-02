import GlobalEmbedding.Paper.SupportedRankKernelGraphVariation

/-!+# The actual kernel family in a fixed onto-kernel chart

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1004–1006 and 1018–1022. Reuse the sole accepted actual kernel graph. Its affine family
parameterizes exactly the original kernel; actual common-radical equations therefore pull
back faithfully. Smoothness holds at every invertible right block, not only the base point.
-/

noncomputable section
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {S W : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [FiniteDimensional ℝ S] [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The actual original kernel family in the accepted kernel graph chart.
Source: `prop:supported-rank`, nearby kernels as graphs over the actual base kernel. -/
def supportedKernelParametrization (B : S →L[ℝ] W) (hB : Function.Surjective B)
    (C : S →L[ℝ] W) : B.ker →L[ℝ] S :=
  B.ker.subtypeL + B.kerᗮ.subtypeL.comp (supportedRankKernelGraph B hB C)

/-- The actual family has exactly the original kernel as its range on the genuine chart.
Source: `prop:supported-rank`, exact local kernel parameterization. -/
theorem supportedKernelParametrization_range (B : S →L[ℝ] W)
    (hB : Function.Surjective B) (C : S →L[ℝ] W) (e : B.kerᗮ ≃L[ℝ] B.kerᗮ)
    (hA : supportedKernelRightBlock (supportedRankKernelChartOperator B hB C) =
      (e : B.kerᗮ →L[ℝ] B.kerᗮ)) :
    (supportedKernelParametrization B hB C).range = C.ker := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    change C ((q : S) + (supportedRankKernelGraph B hB C q : S)) = 0
    exact (supportedRankKernelGraph_mem_kernel_iff B hB C e hA q _).mpr rfl
  · intro hx
    let p := (supportedRankKernelCoordinates B).symm x
    have hp : (p.1 : S) + (p.2 : S) = x :=
      (supportedRankKernelCoordinates B).apply_symm_apply x
    have hz : p.2 = supportedRankKernelGraph B hB C p.1 :=
      (supportedRankKernelGraph_mem_kernel_iff B hB C e hA p.1 p.2).mp (by rw [hp]; exact hx)
    refine ⟨p.1, ?_⟩
    change (p.1 : S) + (supportedRankKernelGraph B hB C p.1 : S) = x
    rw [← hz]
    exact hp

/-- The accepted graph is smooth at EVERY actual invertible right block.
This supplies one common open smooth domain for all orders. The sole block-chart calculus
is reused, with no new inverse differentiation. Source: `prop:supported-rank`, smooth locus. -/
theorem supportedKernelGraph_contDiffAt_of_rightBlock (B : S →L[ℝ] W)
    (hB : Function.Surjective B) (C : S →L[ℝ] W) (e : B.kerᗮ ≃L[ℝ] B.kerᗮ)
    (hA : supportedKernelRightBlock (supportedRankKernelChartOperator B hB C) =
      (e : B.kerᗮ →L[ℝ] B.kerᗮ)) :
    ContDiffAt ℝ ∞ (supportedRankKernelGraph B hB) C := by
  have hchart : ContDiff ℝ ∞ (supportedRankKernelChartOperator B hB) := by fun_prop
  exact (supportedKernelBlockGraph_contDiffAt
    (supportedRankKernelChartOperator B hB C) e hA).comp C hchart.contDiffAt

/-- The actual kernel family is smooth at each point of its genuine chart domain.
Source: `prop:supported-rank`, local smooth common-radical equations. -/
theorem supportedKernelParametrization_contDiffAt (B : S →L[ℝ] W)
    (hB : Function.Surjective B) (C : S →L[ℝ] W) (e : B.kerᗮ ≃L[ℝ] B.kerᗮ)
    (hA : supportedKernelRightBlock (supportedRankKernelChartOperator B hB C) =
      (e : B.kerᗮ →L[ℝ] B.kerᗮ)) :
    ContDiffAt ℝ ∞ (supportedKernelParametrization B hB) C :=
  contDiffAt_const.add (contDiffAt_const.clm_comp
    (supportedKernelGraph_contDiffAt_of_rightBlock B hB C e hA))

/-- The actual common-radical equations agree on the true kernel and its actual family.
Source: `prop:supported-rank`, literal supported-locus zero-set comparison. -/
theorem supportedKernelParametrization_radical_iff
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (M : S →L[ℝ] (V →L[ℝ] V)) (B : S →L[ℝ] W) (hB : Function.Surjective B)
    (C : S →L[ℝ] W) (e : B.kerᗮ ≃L[ℝ] B.kerᗮ)
    (hA : supportedKernelRightBlock (supportedRankKernelChartOperator B hB C) =
      (e : B.kerᗮ →L[ℝ] B.kerᗮ)) (v : V) :
    (∀ q ∈ C.ker, M q v = 0) ↔
      ∀ k : B.ker, M (supportedKernelParametrization B hB C k) v = 0 := by
  rw [← supportedKernelParametrization_range B hB C e hA]
  constructor
  · intro h k
    exact h _ ⟨k, rfl⟩
  · intro h q hq
    obtain ⟨k, rfl⟩ := hq
    exact h k

/-- The actual accepted kernel graph map has a genuinely onto derivative at its base.
Proof: lift `Y` by `Δ=-A Y projection_K`, using the genuine complement inverse and the
accepted exact kernel derivative. Source: `prop:supported-rank`, the kernel-map submersion. -/
theorem supportedKernelGraph_fderiv_surjective (B : S →L[ℝ] W)
    (hB : Function.Surjective B) :
    Function.Surjective (fderiv ℝ (supportedRankKernelGraph B hB) B) := by
  rw [(supportedRankKernelGraph_hasFDerivAt B hB).fderiv]
  intro Y
  refine ⟨-((supportedRankKernelComplementEquiv B hB : B.kerᗮ →L[ℝ] W).comp Y).comp
    B.ker.orthogonalProjectionOnto, ?_⟩
  apply ContinuousLinearMap.ext
  intro k
  simp [supportedRankKernelGraphDerivative]
  exact (supportedRankKernelComplementEquiv B hB).symm_apply_apply (Y k)

end GlobalEmbedding.Paper
