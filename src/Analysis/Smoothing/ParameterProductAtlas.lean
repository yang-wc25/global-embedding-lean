import GlobalEmbedding.Offline.BufferedSmoothing
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# The actual buffered product atlas for nonzero parameter manifolds

Source: the final parameter paragraph of thm:repair, main.tex 778–780.
Both the source and parameter charts are genuine original chart maps.
The common product buffer is their positive minimum, and the same global
buffered integral operator therefore smooths jointly on P × M.
-/

open MeasureTheory GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation

noncomputable section

variable {Ep Es P M : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es]
    [TopologicalSpace P] [TopologicalSpace M]

/-- A product chart index retains the parameter chart first and source chart second. -/
def parameterProductIndex (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (i : Fin (B.count * A.count)) : Fin B.count × Fin A.count :=
  finProdFinEquiv.symm i

/-- Genuine buffered product atlas, with one positive common buffer.
No new coordinate map or chart-dependent scale is supplied as a premise. -/
def parameterProductAtlas (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep) :
    BufferedAtlas (P × M) (Ep × Es) where
  count := B.count * A.count
  chart i := (B.chart (parameterProductIndex A B i).1).prod
    (A.chart (parameterProductIndex A B i).2)
  inner i := B.inner (parameterProductIndex A B i).1 ×ˢ A.inner (parameterProductIndex A B i).2
  inner_open i := (B.inner_open _).prod (A.inner_open _)
  inner_subset i x hx := ⟨B.inner_subset _ hx.1, A.inner_subset _ hx.2⟩
  cover x := by
    obtain ⟨ip, hp⟩ := B.cover x.1
    obtain ⟨is, hs⟩ := A.cover x.2
    refine ⟨finProdFinEquiv (ip,is), ?_⟩
    simpa only [parameterProductIndex, Equiv.symm_apply_apply, Set.mem_prod] using And.intro hp hs
  buffer := min B.buffer A.buffer
  buffer_pos := lt_min B.buffer_pos A.buffer_pos
  buffered i x hx z hz := by
    change z.1 ∈ (B.chart (parameterProductIndex A B i).1).target ∧
      z.2 ∈ (A.chart (parameterProductIndex A B i).2).target
    change dist z ((B.chart (parameterProductIndex A B i).1 x.1,
      A.chart (parameterProductIndex A B i).2 x.2)) < min B.buffer A.buffer at hz
    rw [Prod.dist_eq, max_lt_iff] at hz
    exact ⟨B.buffered _ x.1 hx.1 (hz.1.trans_le (min_le_left _ _)),
      A.buffered _ x.2 hx.2 (hz.2.trans_le (min_le_right _ _))⟩
  support i := B.support (parameterProductIndex A B i).1 ×ˢ A.support (parameterProductIndex A B i).2

variable [ChartedSpace Ep P] [IsManifold 𝓘(ℝ, Ep) ∞ P]
    [ChartedSpace Es M] [IsManifold 𝓘(ℝ, Es) ∞ M]

local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
local instance : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := 𝓘(ℝ, Es)) (n := ∞) P M

/-- Native maximal-atlas compatibility and support subordination are preserved. -/
theorem parameterProductAtlas_smooth (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B) :
    IsSmoothBufferedAtlas (parameterProductAtlas A B) where
  chart_mem i := by
    change (B.chart (parameterProductIndex A B i).1).prod
      (A.chart (parameterProductIndex A B i).2) ∈ IsManifold.maximalAtlas 𝓘(ℝ, Ep × Es) ∞ (P × M)
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hB.chart_mem _) (hA.chart_mem _)
  support_subset i x hx := ⟨hB.support_subset _ hx.1, hA.support_subset _ hx.2⟩

/-- Product transitions act separately in the actual parameter and source variables.
In particular their parameter component does not depend on the source coordinate. -/
theorem parameterProductAtlas_transition (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (i j : Fin (B.count * A.count)) (z : Ep × Es) :
    (parameterProductAtlas A B).chart i ((parameterProductAtlas A B).chart j |>.symm |>.toFun <| z) =
      (B.chart (parameterProductIndex A B i).1 ((B.chart (parameterProductIndex A B j).1).symm z.1),
       A.chart (parameterProductIndex A B i).2 ((A.chart (parameterProductIndex A B j).2).symm z.2)) := rfl

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace Ep] [BorelSpace Ep] [FiniteDimensional ℝ Ep]
    [MeasurableSpace Es] [BorelSpace Es] [FiniteDimensional ℝ Es]

/-- The already constructed global operator gives a genuinely joint smooth map
on P × M for arbitrary parameter dimension. All kernels are sampled within the
same positive product buffer; no separate smooth jets are glued. -/
theorem parameterProductSmoothing_contMDiff
    (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (mu : Measure (Ep × Es)) [mu.IsAddHaarMeasure]
    {K : (Ep × Es) → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin (B.count * A.count) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterProductAtlas A B).inner i)
    {u : P × M → F} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, F) ∞ u) :
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, F) ∞
      (bufferedSmoothing (parameterProductAtlas A B) mu K ell chi u) :=
  bufferedSmoothing_contMDiff (parameterProductAtlas A B) (parameterProductAtlas_smooth A B hA hB)
    mu hK hcompact hsupp hrho hell hell1 chi hchi hchiSupport hu

#print axioms parameterProductAtlas_smooth
#print axioms parameterProductSmoothing_contMDiff

end
end GlobalEmbedding.Continuation
