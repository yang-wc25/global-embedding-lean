import GlobalEmbedding.Paper.MatrixPeriodicPlanarAngle
import GlobalEmbedding.Paper.MatrixOppositeRegularCrossings
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic.FinCases

/-!
# Actual opposite-curvature samples at two distinct cosine levels

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines327–332.
DAG node: `cone-two-cosine-crossing-levels`.
-/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Paper

/-- Genuine finite crossing data on one actual Hopf orbit. The sign flag true is
positive curvature and false is negative curvature. No regular branches are supplied
by a caller: existence is proved below from the actual planar selector. -/
structure MatrixAngularCrossings {C : ℕ} (f : PlanarHopfSphere C → Planar)
    (z : PlanarHopfSphere C) where
  level : Fin 2 → ℝ
  time : Fin 2 → Bool → ℝ
  cos_levels_ne : Real.cos (level 0) ≠ Real.cos (level 1)
  cos_nonzero : ∀ j, Real.cos (level j) ≠ 0
  sin_nonzero : ∀ j, Real.sin (level j) ≠ 0
  velocity_zero : ∀ j b, orbitDeriv planarHopfFlow f (planarHopfFlow (time j b) z) 0 =
    Real.cos (level j)
  velocity_one : ∀ j b, orbitDeriv planarHopfFlow f (planarHopfFlow (time j b) z) 1 =
    Real.sin (level j)
  positive : ∀ j, 0 < planarOrbitCurvature planarHopfFlow f (planarHopfFlow (time j true) z)
  negative : ∀ j, planarOrbitCurvature planarHopfFlow f (planarHopfFlow (time j false) z) < 0

/-- The original two-level opposite samples genuinely exist on every actual orbit. -/
theorem matrix_planar_opposite_samples {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (z : PlanarHopfSphere C) : Nonempty (MatrixAngularCrossings f z) := by
  classical
  obtain ⟨α, hα, hp, hd, hv, hnc⟩ := matrix_planar_periodic_orbit_angle f hf z
  let forbiddenAngles : Set ℝ := {x | Real.sin x = 0 ∨ Real.cos x = 0}
  have hs : Real.sin ⁻¹' ({0} : Set ℝ)ᶜ ∈ Filter.codiscrete ℝ :=
    Real.analyticOnNhd_sin.preimage_zero_mem_codiscrete (x := Real.pi / 2) (by simp)
  have hc : Real.cos ⁻¹' ({0} : Set ℝ)ᶜ ∈ Filter.codiscrete ℝ :=
    Real.analyticOnNhd_cos.preimage_zero_mem_codiscrete (x := 0) (by simp)
  have hD : IsDiscrete forbiddenAngles := by
    have hh := (mem_codiscrete'.mp (inter_mem hs hc)).2
    convert hh using 1
    ext x
    simp [forbiddenAngles]
    tauto
  obtain ⟨l, u, hlu, havoid, hcross⟩ :=
    matrix_periodic_opposite_regular_crossings_avoiding α hα hp hnc forbiddenAngles hD
  have hav (x : ℝ) (hx : x ∈ Ioo l u) : Real.sin x ≠ 0 ∧ Real.cos x ≠ 0 := by
    constructor
    · intro h
      exact Set.disjoint_left.mp havoid hx (Or.inl h)
    · intro h
      exact Set.disjoint_left.mp havoid hx (Or.inr h)
  let a := (l + u) / 2
  have ha : a ∈ Ioo l u := ⟨by dsimp [a]; linarith, by dsimp [a]; linarith⟩
  have hne : -Real.sin a ≠ 0 := neg_ne_zero.mpr (hav a ha).1
  have hcosne : ∀ᶠ b in 𝓝[≠] a, Real.cos b ≠ Real.cos a :=
    (Real.hasDerivAt_cos a).eventually_ne hne
  have hmem : ∀ᶠ b in 𝓝[≠] a, b ∈ Ioo l u :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ha)
  obtain ⟨b, hb, hba⟩ := (hmem.and hcosne).exists
  let level : Fin 2 → ℝ := ![a, b]
  have hlv (j : Fin 2) : level j ∈ Ioo l u := by fin_cases j <;> assumption
  choose p n hpy hny hpos hneg using (fun j : Fin 2 ↦ hcross (level j) (hlv j))
  refine ⟨{
    level := level
    time := fun j flag ↦ if flag then p j else n j
    cos_levels_ne := hba.symm
    cos_nonzero := fun j ↦ (hav _ (hlv j)).2
    sin_nonzero := fun j ↦ (hav _ (hlv j)).1
    velocity_zero := ?_
    velocity_one := ?_
    positive := ?_
    negative := ?_ }⟩
  · intro j flag
    cases flag
    · simpa only [Bool.false_eq_true, ↓reduceIte, hny j] using (hv (n j)).1
    · simpa only [↓reduceIte, hpy j] using (hv (p j)).1
  · intro j flag
    cases flag
    · simpa only [Bool.false_eq_true, ↓reduceIte, hny j] using (hv (n j)).2
    · simpa only [↓reduceIte, hpy j] using (hv (p j)).2
  · intro j
    change 0 < planarOrbitCurvature planarHopfFlow f (planarHopfFlow (p j) z)
    rw [← (hd (p j)).deriv]
    exact hpos j
  · intro j
    change planarOrbitCurvature planarHopfFlow f (planarHopfFlow (n j) z) < 0
    rw [← (hd (n j)).deriv]
    exact hneg j

end GlobalEmbedding.Paper
