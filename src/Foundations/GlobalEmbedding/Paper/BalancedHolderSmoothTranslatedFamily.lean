import GlobalEmbedding.Paper.GlobalSmoothPeriodicHolderFamily
import GlobalEmbedding.Paper.SmoothLocalParameterMap

/-!
# Actual little Hölder smooth parameter and translated families on an open parameter domain

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-holder-smooth-translated-family`.
-/

open Set WithLp
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- A genuine smooth spatially periodic source family on ANY open Euclidean parameter domain
has actual little Hölder slices, smooth in the original norm, jointly with local torus shifts.

Construct each actual slice over the open domain by smooth periodic membership, using zero
outside the domain only to present a total parameter function. Near each parameter p₀ use a
global genuine smooth map R into the domain which is identity near p₀. Composing the source
with R gives a genuine globally smooth periodic family, so the proved global construction
supplies norm-smooth slices and joint shifts. Their exact lift formulas identify these with
the actual chosen slices near p₀. Local equality transfers genuine C∞ to the original open
domain and its product with the Euclidean shift coordinates. No global source regularity
outside the domain is required. Source: jointly smooth slices in the proof of `lem:balanced`. -/
theorem balanced_holder_smooth_translated_family {q a N k : ℕ} {α : ℝ}
    (U : Set (EuclideanSpace ℝ (Fin q))) (hU : IsOpen U)
    (F : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F)
      (U ×ˢ (univ : Set (EuclideanSpace ℝ (Fin a)))))
    (hperiodic : ∀ (p : EuclideanSpace ℝ (Fin q)), p ∈ U →
      ∀ (x : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ),
        F p (x + toLp 2 (fun i ↦ (m i : ℝ))) = F p x)
    (_hα0 : 0 < α) (hα1 : α < 1) :
    ∃ g : EuclideanSpace ℝ (Fin q) → LittlePeriodicCAlphaFunction a N k α,
      (∀ p ∈ U, (g p).val.toFun = F p) ∧ ContDiffOn ℝ ∞ g U ∧
      ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin a) ↦
        littlePeriodicCAlphaTranslateIsometry z.2 (g z.1))
        (U ×ˢ (univ : Set (EuclideanSpace ℝ (Fin a)))) := by
  classical
  have hslice (p : EuclideanSpace ℝ (Fin q)) (hp : p ∈ U) :
      ∃ g : LittlePeriodicCAlphaFunction a N k α, g.val.toFun = F p := by
    have hs : ContDiff ℝ ∞ (F p) := hF.comp_contDiff
      (contDiff_const.prodMk contDiff_id) (fun x ↦ ⟨hp, mem_univ x⟩)
    exact smooth_periodic_little_membership (F p) hs (hperiodic p hp) hα1.le k
  let g (p : EuclideanSpace ℝ (Fin q)) : LittlePeriodicCAlphaFunction a N k α :=
    if hp : p ∈ U then (hslice p hp).choose else 0
  have hg (p : EuclideanSpace ℝ (Fin q)) (hp : p ∈ U) : (g p).val.toFun = F p := by
    simp only [g, dite_eq_left hp]
    exact (hslice p hp).choose_spec
  have hlocal (p₀ : EuclideanSpace ℝ (Fin q)) (hp₀ : p₀ ∈ U) :
      ∃ γ : EuclideanSpace ℝ (Fin q) → LittlePeriodicCAlphaFunction a N k α,
        ContDiff ℝ ∞ γ ∧
        ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin a) ↦
          littlePeriodicCAlphaTranslateIsometry z.2 (γ z.1)) ∧ g =ᶠ[𝓝 p₀] γ := by
    obtain ⟨R, hR, hRU, hRid⟩ := smooth_local_parameter_map U hU p₀ hp₀
    have hG : ContDiff ℝ ∞ (Function.uncurry (fun p ↦ F (R p))) :=
      hF.comp_contDiff ((hR.comp contDiff_fst).prodMk contDiff_snd)
        (fun z ↦ ⟨hRU z.1, mem_univ z.2⟩)
    obtain ⟨γ, hγvalue, hγ, hγshift⟩ := global_smooth_periodic_holder_family
      (fun p ↦ F (R p)) hG (fun p ↦ hperiodic (R p) (hRU p)) hα1.le
    refine ⟨γ, hγ, hγshift, ?_⟩
    filter_upwards [hRid, hU.mem_nhds hp₀] with p hRp hp
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    simp only [hg p hp, hγvalue p, hRp, id_eq]
  refine ⟨g, hg, ?_, ?_⟩
  · intro p hp
    obtain ⟨γ, hγ, hγshift, heq⟩ := hlocal p hp
    exact (hγ.contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt
  · intro z hz
    obtain ⟨γ, hγ, hγshift, heq⟩ := hlocal z.1 hz.1
    have hnear : ∀ᶠ w : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin a) in 𝓝 z,
        g w.1 = γ w.1 := heq.comp_tendsto continuous_fst.continuousAt
    have heqshift : (fun w : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin a) ↦
        littlePeriodicCAlphaTranslateIsometry w.2 (g w.1)) =ᶠ[𝓝 z]
        (fun w ↦ littlePeriodicCAlphaTranslateIsometry w.2 (γ w.1)) :=
      hnear.mono (fun w hw ↦ congrArg (littlePeriodicCAlphaTranslateIsometry w.2) hw)
    exact (hγshift.contDiffAt.congr_of_eventuallyEq heqshift).contDiffWithinAt

#print axioms balanced_holder_smooth_translated_family

end GlobalEmbedding.Paper
