import GlobalEmbedding.Paper.FreeHopfProductNative
import GlobalEmbedding.Paper.PrincipalTorusBundle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The actual smooth torus action on the finite Hopf product

Source: `literature/parallelizable-stable-plus-one/main.tex`, setup:partial, lines216–232.
DAG node: `free-hopf-product-action`.
-/

noncomputable section

open Set WithLp IsManifold
open scoped Manifold ContDiff Topology

namespace GlobalEmbedding.Paper

local instance freeHopfActionTorusAtlas (a : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin a)) (PeriodOneTorus a) :=
  periodicFlatTorusChartedSpace a

local instance freeHopfActionTorusManifold (a : ℕ) :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) ∞ (PeriodOneTorus a) :=
  periodic_flat_torus_isManifold a ∞

/-- The actual quotient torus acts by the original unit complex scalar on each factor. -/
def freeHopfTorusAction {a : ℕ} (C : Fin a → ℕ) (t : PeriodOneTorus a)
    (x : FreeHopfProduct C) : FreeHopfProduct C := fun i ↦
  ⟨(AddCircle.toCircle (t i) : ℂ) • (x i : PlanarHopfAmbient (C i)),
    mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul, Circle.norm_coe, mem_sphere_zero_iff_norm.mp (x i).property, one_mul])⟩

@[simp] theorem freeHopfTorusAction_zero {a : ℕ} (C : Fin a → ℕ)
    (x : FreeHopfProduct C) : freeHopfTorusAction C 0 x = x := by
  funext i
  apply Subtype.ext
  simp [freeHopfTorusAction]

/-- The torus addition law is the actual complex multiplication law, not chosen lifts. -/
theorem freeHopfTorusAction_add {a : ℕ} (C : Fin a → ℕ)
    (s t : PeriodOneTorus a) (x : FreeHopfProduct C) :
    freeHopfTorusAction C (s + t) x = freeHopfTorusAction C s (freeHopfTorusAction C t x) := by
  funext i
  apply Subtype.ext
  simp only [freeHopfTorusAction, PiLp.add_apply, AddCircle.toCircle_add,
    Circle.coe_mul, mul_smul]

/-- This is the additive action of the genuine period-one torus on the actual product. -/
instance freeHopfProductAddAction {a : ℕ} (C : Fin a → ℕ) :
    AddAction (PeriodOneTorus a) (FreeHopfProduct C) where
  vadd := freeHopfTorusAction C
  zero_vadd := freeHopfTorusAction_zero C
  add_vadd := freeHopfTorusAction_add C

/-- Real quotient coordinates recover exactly the original 2π-normalized multi-action. -/
theorem freeHopfTorusAction_real {a : ℕ} (C : Fin a → ℕ)
    (t : EuclideanSpace ℝ (Fin a)) (x : FreeHopfProduct C) :
    freeHopfTorusAction C (toLp 2 (fun i ↦ (t i : AddCircle (1 : ℝ)))) x =
      freeHopfRealAction C (fun i ↦ t i) x := by
  funext i
  apply Subtype.ext
  change (AddCircle.toCircle (t i : AddCircle (1 : ℝ)) : ℂ) • _ = _
  rw [AddCircle.toCircle_apply_mk]
  simp only [div_one]
  rfl

/-- The actual torus action is free because a norm-one sphere vector detects its scalar. -/
theorem freeHopfTorusAction_injective {a : ℕ} (C : Fin a → ℕ)
    (x : FreeHopfProduct C) : Function.Injective (fun t ↦ freeHopfTorusAction C t x) := by
  intro t u h
  apply PiLp.ext
  intro i
  have he := congrArg (fun y : FreeHopfProduct C ↦ (y i : PlanarHopfAmbient (C i))) h
  have hc : (AddCircle.toCircle (t i) : ℂ) = (AddCircle.toCircle (u i) : ℂ) :=
    (smul_left_injective ℂ (ne_zero_of_mem_unit_sphere (x i))) he
  exact AddCircle.injective_toCircle one_ne_zero (Subtype.ext hc)

/-- Joint native smoothness descends through actual torus local quotient inverses.

Proof: at a torus point choose a real lift and its actual native local inverse chart.
The smooth real Hopf multi-action composed with that chart agrees with the quotient
action on a genuine neighborhood, by the actual quotient value identity. No global
lift, chosen orbit origin or assumed smooth action enters the proof.
Source: the whole-product period-one action in setup:partial, lines216–232. -/
theorem freeHopfTorusAction_contMDiff {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin a)).prod (freeHopfModel C))
      (freeHopfModel C) ∞
      (fun p : PeriodOneTorus a × FreeHopfProduct C ↦ freeHopfTorusAction C p.1 p.2) := by
  have hcoords : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) 𝓘(ℝ, Fin a → ℝ) ∞
      (fun t : EuclideanSpace ℝ (Fin a) ↦ fun i ↦ t i) :=
    contMDiff_pi_module_iff.2 (fun i ↦
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin a) i).contMDiff)
  have hreal := (freeHopfRealAction_contMDiff C).comp
    ((hcoords.comp contMDiff_fst).prodMk contMDiff_snd)
  let hf := periodic_flat_torus_local_homeomorph (a := a)
  intro z
  obtain ⟨t, ht⟩ := periodic_flat_torus_projection.surjective z.1
  change toLp 2 (fun i : Fin a ↦ (t i : AddCircle (1 : ℝ))) = z.1 at ht
  let e := hf.localInverseAt t
  have he : e ∈ atlas (EuclideanSpace ℝ (Fin a)) (PeriodOneTorus a) := mem_range_self t
  have hz : z.1 ∈ e.source := by
    have hh := hf.apply_self_mem_localInverseAt_source (x := t)
    rwa [ht] at hh
  have hchart := contMDiffAt_of_mem_maximalAtlas (n := ∞)
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) (subset_maximalAtlas he) hz
  have hlocal : ContMDiffAt
      (𝓘(ℝ, EuclideanSpace ℝ (Fin a)).prod (freeHopfModel C))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin a)).prod (freeHopfModel C)) ∞
      (fun w : PeriodOneTorus a × FreeHopfProduct C ↦ (e w.1, w.2)) z :=
    (hchart.comp z contMDiffAt_fst).prodMk contMDiffAt_snd
  apply ((hreal (e z.1, z.2)).comp z hlocal).congr_of_eventuallyEq
  have hnear : ∀ᶠ w in 𝓝 z, w.1 ∈ e.source :=
    continuous_fst.continuousAt.eventually (e.open_source.mem_nhds hz)
  filter_upwards [hnear] with w hw
  have hp : toLp 2 (fun i : Fin a ↦ (e w.1 i : AddCircle (1 : ℝ))) = w.1 :=
    (congrFun (hf.localInverseAt_symm t) (e w.1)).symm.trans (e.left_inv hw)
  change freeHopfTorusAction C w.1 w.2 = freeHopfRealAction C (fun i ↦ e w.1 i) w.2
  rw [← freeHopfTorusAction_real C (e w.1) w.2, hp]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopfTorusAction_injective
#print axioms GlobalEmbedding.Paper.freeHopfTorusAction_contMDiff
