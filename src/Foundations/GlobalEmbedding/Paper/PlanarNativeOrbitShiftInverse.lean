import GlobalEmbedding.Paper.PlanarOrbitNormalizationData
import GlobalEmbedding.Paper.PlanarSmoothUniqueScalarRoot
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Native smoothness of the same actual global orbit-shift inverse

Source: `main.tex`, `lem:planar`, line 261.
DAG: `planar-native-orbit-shift-inverse`.
The actual scalar inverse was already constructed algebraically. The open
parameter-domain root theorem is reused in each genuine native chart; its
inverse is never asserted smooth outside the chart target. Root uniqueness
identifies these local expressions with the same actual global scalar root.
-/

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace GlobalEmbedding.Paper

variable {P M : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [TopologicalSpace M] [ChartedSpace P M]
    [IsManifold 𝓘(ℝ, P) ∞ M]

/-- The genuine globally chosen scalar orbit-shift root is native smooth.
The only scalar hypotheses concern the actual scalar lift, not a desired
inverse or an independently supplied root function. -/
theorem planarOrbitShiftRoot_contMDiff
    (R : ℝ → M → M)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞
      (fun p : ℝ × M ↦ R p.1 p.2))
    (h : M → ℝ) (hh : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ h)
    (hm : ∀ z, StrictMono (planarOrbitShiftLift R h z))
    (hs : ∀ z, Function.Surjective (planarOrbitShiftLift R h z))
    (hd : ∀ z t, deriv (planarOrbitShiftLift R h z) t ≠ 0) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ (planarOrbitShiftRoot R h hm hs) := by
  intro x
  let e := chartAt P x
  have hx : x ∈ e.source := mem_chart_source P x
  have hxt : e x ∈ e.target := e.map_source hx
  have he : ContMDiffOn 𝓘(ℝ, P) 𝓘(ℝ, P) ∞ e.symm e.target :=
    contMDiffOn_chart_symm
  have hp : ContMDiffOn 𝓘(ℝ, P × ℝ) 𝓘(ℝ, P) ∞
      (fun p : P × ℝ ↦ e.symm p.1) (e.target ×ˢ univ) := by
    exact he.comp contDiff_fst.contMDiff.contMDiffOn (fun p hp ↦ hp.1)
  have ht : ContMDiffOn 𝓘(ℝ, P × ℝ) 𝓘(ℝ, ℝ) ∞
      (fun p : P × ℝ ↦ p.2) (e.target ×ˢ univ) :=
    contDiff_snd.contMDiff.contMDiffOn
  have hfamily : ContMDiffOn 𝓘(ℝ, P × ℝ) 𝓘(ℝ, ℝ) ∞
      (fun p : P × ℝ ↦ planarOrbitShiftLift R h (e.symm p.1) p.2)
      (e.target ×ˢ univ) := by
    exact ht.add (hh.comp_contMDiffOn (hR.comp_contMDiffOn (ht.prodMk hp)))
  have hroots : ContDiffOn ℝ ∞
      (fun p : P ↦ planarOrbitShiftRoot R h hm hs (e.symm p)) e.target := by
    have hr := planar_scalar_root_contDiffOn e.target e.open_target
      (fun p : P ↦ planarOrbitShiftLift R h (e.symm p)) hfamily.contDiffOn
      (fun p ↦ hm (e.symm p)) (fun p ↦ hs (e.symm p))
      (fun p _ t ↦ hd (e.symm p) t)
    simpa only [planarOrbitShiftRoot, planarOrbitShiftLiftIso] using hr
  have hrootAt : ContDiffAt ℝ ∞
      (fun p : P ↦ planarOrbitShiftRoot R h hm hs (e.symm p)) (e x) :=
    hroots.contDiffAt (e.open_target.mem_nhds hxt)
  have hchart : ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, P) ∞ e x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hx
  have hcomp := hrootAt.comp_contMDiffAt hchart
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  exact congrArg (planarOrbitShiftRoot R h hm hs) (e.left_inv hy).symm

/-- The same canonical global orbit-shift equivalence has a genuinely native
smooth inverse. It is literally R_(actual scalar root(z))z. -/
theorem planarOrbitShiftEquiv_symm_contMDiff
    (R : ℝ → M → M)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞
      (fun p : ℝ × M ↦ R p.1 p.2))
    (h : M → ℝ) (hh : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ h)
    (hm : ∀ z, StrictMono (planarOrbitShiftLift R h z))
    (hs : ∀ z, Function.Surjective (planarOrbitShiftLift R h z))
    (hd : ∀ z t, deriv (planarOrbitShiftLift R h z) t ≠ 0) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, P) ∞
      (planarOrbitShiftEquiv R hzero hadd h hm hs).symm := by
  have hr := planarOrbitShiftRoot_contMDiff R hR h hh hm hs hd
  exact hR.comp (hr.prodMk contMDiff_id)

/-- Actual positive lift derivatives, the genuine period-one action and
actual native smooth R/h prove smoothness of the same constructed positive
orbit-shift inverse. Strict monotonicity and surjectivity are derived by the
already accepted period-one scalar calculus, not added as final hypotheses. -/
theorem planarPositiveOrbitShiftEquiv_symm_contMDiff
    (R : ℝ → M → M)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞
      (fun p : ℝ × M ↦ R p.1 p.2))
    (h : M → ℝ) (hh : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ h)
    (hc : ∀ z, Continuous (planarOrbitShiftLift R h z))
    (hpos : ∀ z t, 0 < deriv (planarOrbitShiftLift R h z) t) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, P) ∞
      (planarPositiveOrbitShiftEquiv R hzero hadd hone h hc hpos).symm := by
  exact planarOrbitShiftEquiv_symm_contMDiff R hzero hadd hR h hh
    (planarOrbitShiftLift_strictMono R h hpos)
    (planarOrbitShiftLift_surjective R hadd hone h hc)
    (fun z t ↦ ne_of_gt (hpos z t))

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.planarOrbitShiftRoot_contMDiff
#print axioms GlobalEmbedding.Paper.planarOrbitShiftEquiv_symm_contMDiff
#print axioms GlobalEmbedding.Paper.planarPositiveOrbitShiftEquiv_symm_contMDiff
