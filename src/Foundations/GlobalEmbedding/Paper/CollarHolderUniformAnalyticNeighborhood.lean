import GlobalEmbedding.Paper.LittlePeriodicCAlphaSpace
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Topology.MetricSpace.Thickening

/-!
# A common base neighborhood for joint analyticity on the entire real torus orbit

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Actual periodicity makes the real orbit compact modulo integer shifts.
-/

open Set Filter Metric WithLp

namespace GlobalEmbedding.Paper

/-- Joint analyticity at every point of one base fiber of an actual real little Hölder family
extends to a common positive base neighborhood and the entire real orbit.

Source: Proposition `prop:collar`, proof lines 530–534. The analytic locus of the actual lift
is genuinely open. The original functions' actual integer periodicity makes this locus invariant
under integer orbit shifts, by analytic composition with translations and their inverses.
The compact fundamental real cube in the base fiber lies in this open locus; a positive
thickening therefore lies there. For every sufficiently close base and every real orbit point,
reduce the orbit coordinates by their integer parts. The reduced point is uniformly near that
compact cube, hence analytic. Integer invariance returns the original point. No common base
neighborhood, joint lift continuity or Hölder-family continuity is an extra assumption. -/
theorem collar_holder_uniform_analytic_neighborhood
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {a N k : ℕ} {α : ℝ}
    (u : P → LittlePeriodicCAlphaFunction a N k α) (p₀ : P)
    (hu : ∀ y : EuclideanSpace ℝ (Fin a),
      AnalyticAt ℝ (fun z : P × EuclideanSpace ℝ (Fin a) ↦
        (u z.1).val.toFun z.2) (p₀, y)) :
    ∃ ε : ℝ, 0 < ε ∧ AnalyticOnNhd ℝ
      (fun z : P × EuclideanSpace ℝ (Fin a) ↦ (u z.1).val.toFun z.2)
      (Metric.ball p₀ ε ×ˢ univ) := by
  let F : P × EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N) :=
    fun z ↦ (u z.1).val.toFun z.2
  let A : Set (P × EuclideanSpace ℝ (Fin a)) := {z | AnalyticAt ℝ F z}
  have hA : IsOpen A := isOpen_analyticAt ℝ F
  let v (t : Fin a → ℤ) : P × EuclideanSpace ℝ (Fin a) :=
    (0, toLp 2 (fun i ↦ (t i : ℝ)))
  have hperiod (z : P × EuclideanSpace ℝ (Fin a)) (t : Fin a → ℤ) : F (z + v t) = F z := by
    change (u (z.1 + 0)).val.toFun (z.2 + toLp 2 (fun i ↦ (t i : ℝ))) = _
    rw [add_zero]
    exact (u z.1).val.periodic z.2 t
  have hinv (z : P × EuclideanSpace ℝ (Fin a)) (t : Fin a → ℤ) :
      z + v t ∈ A ↔ z ∈ A := by
    have hplus : (fun w ↦ F (w + v t)) = F := funext (fun w ↦ hperiod w t)
    have hminus : (fun w ↦ F (w - v t)) = F := by
      funext w
      have he := hperiod (w - v t) t
      simpa only [sub_add_cancel] using he.symm
    constructor
    · intro hz
      change AnalyticAt ℝ F (z + v t) at hz
      change AnalyticAt ℝ F z
      have he : AnalyticAt ℝ (fun w ↦ F (w + v t)) z :=
        hz.comp (f := fun w ↦ w + v t) (x := z) (analyticAt_id.add analyticAt_const)
      simpa only [hplus] using he
    · intro hz
      change AnalyticAt ℝ F z at hz
      change AnalyticAt ℝ F (z + v t)
      have he : AnalyticAt ℝ (fun w ↦ F (w - v t)) (z + v t) :=
        hz.comp_of_eq (analyticAt_id.sub analyticAt_const) (add_sub_cancel_right z (v t))
      simpa only [hminus] using he
  let φ (x : Fin a → ℝ) : P × EuclideanSpace ℝ (Fin a) := (p₀, toLp 2 x)
  have hφ : Continuous φ := continuous_const.prodMk (PiLp.continuous_toLp _ _)
  let K := φ '' Icc (0 : Fin a → ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image hφ
  have hKA : K ⊆ A := by
    rintro _ ⟨x, _, rfl⟩
    exact hu (toLp 2 x)
  obtain ⟨ε, hε, hεA⟩ := hK.exists_thickening_subset_open hA hKA
  refine ⟨ε, hε, ?_⟩
  intro z hz
  let x : EuclideanSpace ℝ (Fin a) := toLp 2 (fun i ↦ Int.fract (z.2 i))
  let t : Fin a → ℤ := fun i ↦ ⌊z.2 i⌋
  have hx : (fun i ↦ Int.fract (z.2 i)) ∈ Icc (0 : Fin a → ℝ) 1 :=
    ⟨fun _ ↦ Int.fract_nonneg _, fun _ ↦ (Int.fract_lt_one _).le⟩
  have hmem : (p₀, x) ∈ K := ⟨_, hx, rfl⟩
  have hdist : dist (z.1, x) (p₀, x) < ε := by
    simpa only [Metric.mem_ball, Prod.dist_eq, dist_self,
      max_eq_left (dist_nonneg)] using hz.1
  have hred : (z.1, x) ∈ A := hεA (mem_thickening_iff.mpr ⟨_, hmem, hdist⟩)
  have hpoint : (z.1, x) + v t = z := by
    apply Prod.ext
    · exact add_zero z.1
    · ext i
      exact Int.fract_add_floor _
  exact hpoint ▸ (hinv (z.1, x) t).mpr hred

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_holder_uniform_analytic_neighborhood
