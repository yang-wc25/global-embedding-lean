import GlobalEmbedding.Paper.PrincipalTorusBundle
import GlobalEmbedding.Paper.PrincipalTorusVerticalCalculus

/-!
# Actual translations on overlaps of native principal-torus charts

Source: `main.tex`, proof of `lem:balanced`, line418. All shifts below are derived from
actual equivariant bundle charts and their inverses. They are not extra transport data.
-/

noncomputable section
open Set WithLp
open scoped Manifold ContDiff
namespace GlobalEmbedding.Paper
local instance principalTorusOverlapChartedSpace (a : ℕ) : ChartedSpace (EuclideanSpace ℝ (Fin a)) (PeriodOneTorus a) :=
  periodicFlatTorusChartedSpace a
local instance principalTorusOverlapIsManifold (a : ℕ) : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) ∞ (PeriodOneTorus a) :=
  periodic_flat_torus_isManifold a ∞

variable {E H EB HB M B ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace B] [ChartedSpace HB B]
namespace PrincipalTorusBundle
variable {a : ℕ} {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ EB HB}
  {π : M → B} [IsManifold I ∞ M] [IsManifold J ∞ B]
  [AddAction (PeriodOneTorus a) M]
  (S : PrincipalTorusBundle (ι := ι) a I J π)
include S

/-- A point of the actual fiber in one native local chart. -/
def fiberChartPoint (i : ι) (b : B) (q : PeriodOneTorus a) : M :=
  (S.trivialization i).toOpenPartialHomeomorph.symm (b, q)

theorem fiberChartPoint_mem_source (i : ι) {b : B}
    (hb : b ∈ (S.trivialization i).baseSet) (q : PeriodOneTorus a) :
    S.fiberChartPoint i b q ∈ (S.trivialization i).source :=
  (S.trivialization i).map_target ((S.trivialization i).mem_target.mpr hb)

theorem projection_fiberChartPoint (i : ι) {b : B}
    (hb : b ∈ (S.trivialization i).baseSet) (q : PeriodOneTorus a) :
    π (S.fiberChartPoint i b q) = b :=
  (S.trivialization i).proj_symm_apply' hb

theorem chart_fiberChartPoint (i : ι) {b : B}
    (hb : b ∈ (S.trivialization i).baseSet) (q : PeriodOneTorus a) :
    S.trivialization i (S.fiberChartPoint i b q) = (b, q) :=
  (S.trivialization i).apply_symm_apply' hb

/-- Native inverse charts intertwine the original action and actual torus translation. -/
theorem action_fiberChartPoint (i : ι) {b : B}
    (hb : b ∈ (S.trivialization i).baseSet) (q t : PeriodOneTorus a) :
    t +ᵥ S.fiberChartPoint i b q = S.fiberChartPoint i b (q + t) := by
  apply (S.trivialization i).toOpenPartialHomeomorph.injOn
    (S.action_mem_source i _ (S.fiberChartPoint_mem_source i hb q) t)
    (S.fiberChartPoint_mem_source i hb (q + t))
  change S.trivialization i (t +ᵥ S.fiberChartPoint i b q) =
    S.trivialization i (S.fiberChartPoint i b (q + t))
  rw [S.action_coord i _ (S.fiberChartPoint_mem_source i hb q) t,
    S.projection_fiberChartPoint i hb q, S.chart_fiberChartPoint i hb q,
    S.chart_fiberChartPoint i hb (q + t)]

/-- The genuine torus-valued shift from chart i to chart j, defined at its zero section. -/
def overlapShift (i j : ι) (b : B) : PeriodOneTorus a :=
  (S.trivialization j (S.fiberChartPoint i b 0)).2

/-- On the actual overlap the full change of coordinates is this torus translation. -/
theorem overlap_chart (i j : ι) {b : B}
    (hi : b ∈ (S.trivialization i).baseSet)
    (hj : b ∈ (S.trivialization j).baseSet) (q : PeriodOneTorus a) :
    S.trivialization j (S.fiberChartPoint i b q) = (b, q + S.overlapShift i j b) := by
  have hz : S.fiberChartPoint i b 0 ∈ (S.trivialization j).source := by
    apply (S.trivialization j).mem_source.mpr
    rw [S.projection_fiberChartPoint i hi 0]
    exact hj
  have he := S.action_fiberChartPoint i hi 0 q
  rw [zero_add] at he
  rw [← he, S.action_coord j _ hz q, S.projection_fiberChartPoint i hi 0]
  simp only [overlapShift, add_comm]

/-- The same actual point has these related native fiber coordinates. -/
theorem fiberChartPoint_overlap (i j : ι) {b : B}
    (hi : b ∈ (S.trivialization i).baseSet)
    (hj : b ∈ (S.trivialization j).baseSet) (q : PeriodOneTorus a) :
    S.fiberChartPoint i b q = S.fiberChartPoint j b (q + S.overlapShift i j b) := by
  have hz : S.fiberChartPoint i b q ∈ (S.trivialization j).source := by
    apply (S.trivialization j).mem_source.mpr
    rw [S.projection_fiberChartPoint i hi q]
    exact hj
  have he : (S.trivialization j).toOpenPartialHomeomorph.symm
      (S.trivialization j (S.fiberChartPoint i b q)) = S.fiberChartPoint i b q :=
    (S.trivialization j).toOpenPartialHomeomorph.left_inv hz
  rw [S.overlap_chart i j hi hj q] at he
  exact he.symm

/-- Every genuine global source datum has exactly the induced local translation relation. -/
theorem source_pullback_overlap {V : Type*} (F : M → V) (i j : ι) {b : B}
    (hi : b ∈ (S.trivialization i).baseSet)
    (hj : b ∈ (S.trivialization j).baseSet) (q : PeriodOneTorus a) :
    F (S.fiberChartPoint i b q) = F (S.fiberChartPoint j b (q + S.overlapShift i j b)) :=
  congrArg F (S.fiberChartPoint_overlap i j hi hj q)

/-- The actual base-dependent overlap shift is smooth on its genuine open overlap. -/
theorem contMDiffOn_overlapShift (i j : ι) :
    ContMDiffOn J 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) ∞ (S.overlapShift i j)
      ((S.trivialization i).baseSet ∩ (S.trivialization j).baseSet) := by
  have hp : ContMDiffOn J I ∞ (fun b : B ↦ S.fiberChartPoint i b 0)
      (S.trivialization i).baseSet :=
    (S.smooth_inverse i).comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun b hb ↦ (S.trivialization i).mem_target.mpr hb)
  have hc := (S.smooth_trivialization j).comp (hp.mono inter_subset_left)
    (show ∀ b ∈ (S.trivialization i).baseSet ∩ (S.trivialization j).baseSet,
      S.fiberChartPoint i b 0 ∈ (S.trivialization j).source by
      intro b hb
      apply (S.trivialization j).mem_source.mpr
      rw [S.projection_fiberChartPoint i hb.1 0]
      exact hb.2)
  exact contMDiff_snd.comp_contMDiffOn hc

#print axioms contMDiffOn_overlapShift
#print axioms action_fiberChartPoint
#print axioms overlap_chart
#print axioms source_pullback_overlap
end PrincipalTorusBundle
end GlobalEmbedding.Paper
