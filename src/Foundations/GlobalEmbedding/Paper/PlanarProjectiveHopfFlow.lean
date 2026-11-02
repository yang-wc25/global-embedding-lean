import GlobalEmbedding.Paper.PlanarAntipodalSmoothAtlas
import GlobalEmbedding.Paper.PlanarHopfFlow

/-!
# The actual descended projective Hopf flow

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines258–259.
DAG node: `planar-projective-hopf-flow`.
-/
noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter
namespace GlobalEmbedding.Paper

/-- The genuine Hopf action commutes with the actual sphere antipode. -/
@[simp] theorem planarHopfFlow_neg {C : ℕ} (t : ℝ) (z : PlanarHopfSphere C) :
    planarHopfFlow t (-z) = -(planarHopfFlow t z) := by
  apply Subtype.ext
  simp [planarHopfFlow_coe]

/-- The genuine projective Hopf flow is actual quotient recursion of the sphere flow. -/
def planarProjectiveHopfFlow {C : ℕ} (t : ℝ) :
    PlanarRealProjective C → PlanarRealProjective C :=
  Quotient.map (planarHopfFlow t) (fun z w h ↦ by
    apply Quotient.exact
    apply (planarAntipodalProjection_eq_iff _ _).mpr
    rcases (planarAntipodalProjection_eq_iff z w).mp (Quotient.sound h) with hzw | hzw
    · exact Or.inl (congrArg (planarHopfFlow t) hzw)
    · exact Or.inr (by rw [hzw, planarHopfFlow_neg]))

/-- The actual projection intertwines the sphere and projective flows literally. -/
@[simp] theorem planarProjectiveHopfFlow_projection {C : ℕ} (t : ℝ)
    (z : PlanarHopfSphere C) :
    planarProjectiveHopfFlow t (planarAntipodalProjection z) =
      planarAntipodalProjection (planarHopfFlow t z) := rfl

@[simp] theorem planarProjectiveHopfFlow_zero {C : ℕ} (x : PlanarRealProjective C) :
    planarProjectiveHopfFlow 0 x = x := by
  induction x using Quotient.inductionOn with
  | _ z => exact congrArg planarAntipodalProjection (planarHopfFlow_zero z)

/-- Addition is the genuine additive time flow law on the quotient. -/
theorem planarProjectiveHopfFlow_add {C : ℕ} (s t : ℝ) (x : PlanarRealProjective C) :
    planarProjectiveHopfFlow (s + t) x =
      planarProjectiveHopfFlow s (planarProjectiveHopfFlow t x) := by
  induction x using Quotient.inductionOn with
  | _ z => exact congrArg planarAntipodalProjection (planarHopfFlow_add s t z)

@[simp] theorem planarProjectiveHopfFlow_one {C : ℕ} (x : PlanarRealProjective C) :
    planarProjectiveHopfFlow 1 x = x := by
  induction x using Quotient.inductionOn with
  | _ z => exact congrArg planarAntipodalProjection (planarHopfFlow_one z)

/-- The antipodal half-period becomes an actual identity downstairs. -/
@[simp] theorem planarProjectiveHopfFlow_half {C : ℕ} (x : PlanarRealProjective C) :
    planarProjectiveHopfFlow (1 / 2) x = x := by
  induction x using Quotient.inductionOn with
  | _ z =>
    change planarAntipodalProjection (planarHopfFlow (1 / 2) z) = planarAntipodalProjection z
    rw [planarHopfFlow_half, planarAntipodalProjection_neg]

/-- Native joint smoothness is proved by the actual smooth covering local inverse,
rather than imposed as a structure field on an arbitrary quotient action. -/
theorem planarProjectiveHopfFlow_contMDiff (C : ℕ) [Fact (0 < C)] :
    ContMDiff (𝓘(ℝ, ℝ).prod (planarHopfModel C)) (planarHopfModel C) ∞
      (fun p : ℝ × PlanarRealProjective C ↦ planarProjectiveHopfFlow p.1 p.2) := by
  intro p
  obtain ⟨z₀, hz₀⟩ := planarAntipodalProjection_surjective C p.2
  let hf := planarAntipodalLocalHomeomorph C
  let L := hf.localInverseAt z₀
  have hx : p.2 ∈ L.source := by
    rw [← hz₀]
    exact hf.apply_self_mem_localInverseAt_source
  have hL : ContMDiffAt (planarHopfModel C) (planarHopfModel C) ∞ L p.2 :=
    (planarAntipodalLocalInverse_contMDiffOn z₀).contMDiffAt (L.open_source.mem_nhds hx)
  have hs : ContMDiffAt (𝓘(ℝ, ℝ).prod (planarHopfModel C))
      (𝓘(ℝ, ℝ).prod (planarHopfModel C)) ∞
      (fun r : ℝ × PlanarRealProjective C ↦ (r.1, L r.2)) p :=
    contMDiffAt_fst.prodMk (hL.comp p contMDiffAt_snd)
  have hflow := (planarAntipodalProjection_contMDiff C).comp (planarHopfFlow_contMDiff C)
  have hh := hflow.contMDiffAt.comp p hs
  have he : (fun r : ℝ × PlanarRealProjective C ↦ planarProjectiveHopfFlow r.1 r.2)
      =ᶠ[𝓝 p] (fun r ↦ planarAntipodalProjection (planarHopfFlow r.1 (L r.2))) := by
    filter_upwards [continuous_snd.continuousAt (L.open_source.mem_nhds hx)] with r hr
    have heL : planarAntipodalProjection (L r.2) = r.2 :=
      hf.apply_localInverseAt_of_mem hr
    calc
      _ = planarProjectiveHopfFlow r.1 (planarAntipodalProjection (L r.2)) :=
        congrArg (planarProjectiveHopfFlow r.1) heL.symm
      _ = _ := planarProjectiveHopfFlow_projection r.1 (L r.2)
  exact hh.congr_of_eventuallyEq he

/-- The actual descended jointly smooth period-one flow, with all laws proved above. -/
def planarProjectiveSmoothFlow (C : ℕ) [Fact (0 < C)] :
    PeriodOneSmoothFlow (planarHopfModel C) (PlanarRealProjective C) where
  flow := planarProjectiveHopfFlow
  flow_zero := planarProjectiveHopfFlow_zero
  flow_add := planarProjectiveHopfFlow_add
  flow_one := planarProjectiveHopfFlow_one
  smooth := planarProjectiveHopfFlow_contMDiff C

end GlobalEmbedding.Paper
