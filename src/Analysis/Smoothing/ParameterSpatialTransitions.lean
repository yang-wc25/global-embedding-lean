import Smoothing.ParameterProductAtlas
import GlobalEmbedding.Paper.IncrementsJointSpatialJets
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# True first and second spatial jets under product chart transitions

Source: main.tex 778: product transitions preserve spatial differentiation.
The second formula retains the first derivative times the second derivative
of the source transition. No parameter derivative of the map is introduced.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Filter Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation
noncomputable section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The exact local second chain rule for native Frechet derivatives. -/
theorem parameter_second_fderiv_comp
    {f : F → G} {g : E → F} {U : Set E} {V : Set F}
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f V) (hg : ContDiffOn ℝ ∞ g U)
    (hmap : MapsTo g U V) {x : E} (hx : x ∈ U) (v w : E) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) x v w =
      fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) +
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) := by
  have hge := (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdf := hf.fderiv_of_isOpen hV (m := ∞) (by simp)
  have hdg := hg.fderiv_of_isOpen hU (m := ∞) (by simp)
  have heq : fderiv ℝ (f ∘ g) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ f (g y)).comp (fderiv ℝ g y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_comp y ((hf.contDiffAt (hV.mem_nhds (hmap hy))).differentiableAt (by simp))
      ((hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
  rw [heq.fderiv_eq]
  have hc := ((hdf.contDiffAt (hV.mem_nhds (hmap hx))).differentiableAt (by simp)).hasFDerivAt.comp x
    hge.hasFDerivAt
  have hd := ((hdg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hh := (hc.clm_comp hd).fderiv
  exact congrArg (fun L => L v w) hh

variable {Ep Es Ep' Es' Y : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es]
    [NormedAddCommGroup Ep'] [NormedSpace ℝ Ep']
    [NormedAddCommGroup Es'] [NormedSpace ℝ Es']
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- First spatial derivative through a product transition uses only the
first spatial derivative of u and source transition. The parameter coordinate
may be any map a; no derivative of a occurs in this formula. -/
theorem parameter_product_spatial_first
    (a : Ep → Ep') {b : Es → Es'} {u : Ep' × Es' → Y}
    {U : Set Es} {V : Set (Ep' × Es')} (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V) (hb : ContDiffOn ℝ ∞ b U)
    (p : Ep) (hmap : ∀ x ∈ U, (a p,b x) ∈ V) {x : Es} (hx : x ∈ U) :
    fderiv ℝ (fun y => u (a p,b y)) x =
      (fderiv ℝ (fun y : Es' => u (a p,y)) (b x)).comp (fderiv ℝ b x) := by
  have hs : ContDiffOn ℝ ∞ (fun y : Es' => u (a p,y))
      ((fun y : Es' => (a p,y)) ⁻¹' V) :=
    hu.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => hy)
  exact fderiv_comp x
    ((hs.contDiffAt ((hV.preimage (continuous_const.prodMk continuous_id)).mem_nhds (hmap x hx))).differentiableAt (by simp))
    ((hb.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))

/-- Second spatial derivative retains the transition Hessian term. This is
an equality for the same original map composed with the product transition. -/
theorem parameter_product_spatial_second
    (a : Ep → Ep') {b : Es → Es'} {u : Ep' × Es' → Y}
    {U : Set Es} {V : Set (Ep' × Es')} (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V) (hb : ContDiffOn ℝ ∞ b U)
    (p : Ep) (hmap : ∀ x ∈ U, (a p,b x) ∈ V) {x : Es} (hx : x ∈ U)
    (v w : Es) :
    fderiv ℝ (fderiv ℝ (fun y => u (a p,b y))) x v w =
      fderiv ℝ (fun y : Es' => u (a p,y)) (b x) (fderiv ℝ (fderiv ℝ b) x v w) +
      fderiv ℝ (fderiv ℝ (fun y : Es' => u (a p,y))) (b x)
        (fderiv ℝ b x v) (fderiv ℝ b x w) := by
  have hs : ContDiffOn ℝ ∞ (fun y : Es' => u (a p,y))
      ((fun y : Es' => (a p,y)) ⁻¹' V) :=
    hu.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => hy)
  exact parameter_second_fderiv_comp hU
    (hV.preimage (continuous_const.prodMk continuous_id)) hs hb (fun y hy => hmap y hy) hx v w

#print axioms parameter_product_spatial_first
#print axioms parameter_product_spatial_second

end
end GlobalEmbedding.Continuation
