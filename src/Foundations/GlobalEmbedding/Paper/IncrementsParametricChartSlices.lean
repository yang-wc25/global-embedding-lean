import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# SAME local parameter-preserving adapted chart: slice/atlas consumer

Source: `main.tex`, lem:increments594–617 and finite-auxiliary-parameter clause.
DAG: `increments-parametric-chart-slices`. Exclusive worker W2, child5B.
STAGE2 ONLY for ROOT lock; the sole named proof hole is expected.
W5 owns the augmented local producer. No second IFT or global extension.
-/

noncomputable section
open Manifold Set
open scoped ContDiff
namespace GlobalEmbedding.Paper

variable {m : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "𝓙" => 𝓘(ℝ, D)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]

/-- Slice the SAME actual jointly smooth parameter-preserving local chart,
retaining its literal domains and original phase coordinate. Its existence
and smoothness are genuine internal outputs of the separate local producer,
not new assumptions on the original final target. Empty slices are permitted.

Natural-language proof, pending ROOT exact lock: at a true target point,
apply congrArg Prod.fst to a.right_inv and forward parameter preservation at
the actual inverse point; this gives inverse parameter preservation. For
each fixed p construct the partial homeomorphism with source/target equal to
the literal preimages of a.source/a.target under x ↦ (p,x), and forward/inverse
maps equal to snd of a(p,x)/a.symm(p,y). Native map_source/map_target and
left_inv/right_inv, using only that parameter identity on actual domains,
give the partial equivalence laws. Open preimages and native joint continuity
give the partial homeomorphism fields. Restrict both original joint smooth
maps along the native constant-p embeddings and project snd. Invoke existing
OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn for each actual slice.
The SAME inverse projection gives joint inverse smoothness, full inverse
identity and MapsTo; the given phase coordinate and right_inv give hadapt.

There is no IFT, chosen second inverse, nonempty every-p domain, whole-parameter
smooth extension, uniform radius or quantitative profile assertion. For the
normed local producer take M=D; on the original manifold use native composition
with its genuine original spatial chart. Original adapted-cover/admissibility,
conditioning and full increments remain separate. Source: actual adapted
coordinates and finite-parameter clause of original lem:increments. -/
theorem incrementsParametricChart_slices
    (a : OpenPartialHomeomorph (Ep × M) (Ep × D)) (ψ : Ep → M → ℝ)
    (hparam : ∀ z ∈ a.source, (a z).1 = z.1)
    (hphase : ∀ z ∈ a.source, (a z).2 0 = ψ z.1 z.2)
    (ha : ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, Ep × D) ∞ a a.source)
    (hai : ContMDiffOn 𝓘(ℝ, Ep × D) ((𝓘(ℝ, Ep)).prod 𝓙) ∞ a.symm a.target) :
    ∃ e : Ep → OpenPartialHomeomorph M D,
      (∀ p, (e p).source = {x | (p, x) ∈ a.source}) ∧
      (∀ p, (e p).target = {y | (p, y) ∈ a.target}) ∧
      (∀ p x, e p x = (a (p, x)).2) ∧
      (∀ p y, (e p).symm y = (a.symm (p, y)).2) ∧
      (∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M) ∧
      ContMDiffOn 𝓘(ℝ, Ep × D) 𝓙 ∞
        (fun z : Ep × D ↦ (e z.1).symm z.2) a.target ∧
      (∀ z ∈ a.target, a.symm z = (z.1, (e z.1).symm z.2)) ∧
      MapsTo (fun z : Ep × D ↦ (z.1, (e z.1).symm z.2)) a.target a.source ∧
      (∀ z ∈ a.target, ψ z.1 ((e z.1).symm z.2) = z.2 0) := by
  have hfirst {z : Ep × D} (hz : z ∈ a.target) : (a.symm z).1 = z.1 := by
    rw [← hparam (a.symm z) (a.map_target hz), a.right_inv hz]
  have hpair {z : Ep × M} (hz : z ∈ a.source) : (z.1, (a z).2) = a z :=
    Prod.ext (hparam z hz).symm rfl
  have hipair {z : Ep × D} (hz : z ∈ a.target) : (z.1, (a.symm z).2) = a.symm z :=
    Prod.ext (hfirst hz).symm rfl
  let e : Ep → OpenPartialHomeomorph M D := fun p ↦ {
    toFun := fun x ↦ (a (p, x)).2
    invFun := fun y ↦ (a.symm (p, y)).2
    source := {x | (p, x) ∈ a.source}
    target := {y | (p, y) ∈ a.target}
    map_source' := by
      intro x hx
      change (p, (a (p, x)).2) ∈ a.target
      rw [hpair hx]
      exact a.map_source hx
    map_target' := by
      intro y hy
      change (p, (a.symm (p, y)).2) ∈ a.source
      rw [hipair hy]
      exact a.map_target hy
    left_inv' := by
      intro x hx
      rw [hpair hx]
      exact congrArg Prod.snd (a.left_inv hx)
    right_inv' := by
      intro y hy
      rw [hipair hy]
      exact congrArg Prod.snd (a.right_inv hy)
    open_source := a.open_source.preimage (continuous_const.prodMk continuous_id)
    open_target := a.open_target.preimage (continuous_const.prodMk continuous_id)
    continuousOn_toFun := continuous_snd.comp_continuousOn
      (a.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx ↦ hx))
    continuousOn_invFun := continuous_snd.comp_continuousOn
      (a.continuousOn_symm.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun _ hy ↦ hy)) }
  have his : ContMDiffOn 𝓘(ℝ, Ep × D) 𝓙 ∞ (fun z ↦ (a.symm z).2) a.target :=
    ((contMDiffOn_prod_iff _).mp hai).2
  refine ⟨e, fun _ ↦ rfl, fun _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, ?_, his,
    fun z hz ↦ (hipair hz).symm, ?_, ?_⟩
  · intro p
    apply (e p).mem_maximalAtlas_of_contMDiffOn
    · have hfix : ContMDiff 𝓙 ((𝓘(ℝ, Ep)).prod 𝓙) ∞ (fun x : M ↦ (p, x)) :=
        contMDiff_const.prodMk contMDiff_id
      exact ((contMDiffOn_prod_module_iff _).mp
        (ha.comp hfix.contMDiffOn (fun _ hx ↦ hx))).2
    · have hfix : ContMDiff 𝓙 𝓘(ℝ, Ep × D) ∞ (fun y : D ↦ (p, y)) :=
        (contDiff_const.prodMk contDiff_id).contMDiff
      exact his.comp hfix.contMDiffOn (fun _ hy ↦ hy)
  · intro z hz
    change (z.1, (a.symm z).2) ∈ a.source
    rw [hipair hz]
    exact a.map_target hz
  · intro z hz
    change ψ z.1 (a.symm z).2 = z.2 0
    have h := hphase (a.symm z) (a.map_target hz)
    rw [a.right_inv hz, hfirst hz] at h
    exact h.symm

end GlobalEmbedding.Paper
