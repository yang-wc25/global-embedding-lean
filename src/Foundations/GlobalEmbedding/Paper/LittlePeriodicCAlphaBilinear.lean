import GlobalEmbedding.Paper.PeriodicCAlphaBilinearContinuous
import GlobalEmbedding.Paper.LittlePeriodicCAlphaSpace

/-!
# The actual bounded bilinear product on the original little Hölder closures

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 396–418.
DAG node: `balanced-holder-little-bilinear-product`.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Pointwise multiplication by a fixed continuous bilinear value map restricts to a genuine
bounded bilinear map on the actual little Hölder spaces, for α≤1.

The constructed ambient bilinear product is jointly continuous and preserves pairs of genuine
smooth lifts. Therefore it maps the product of their closures into the output smooth closure.
Restrict its exact product values, inherit both linearities, and use the ambient operator norm
for a uniform bilinear bound. Source: smooth approximation in `lem:balanced`. -/
noncomputable def littlePeriodicCAlphaBilinear {a M N L k : ℕ} {α : ℝ}
    (B : EuclideanSpace ℝ (Fin M) →L[ℝ]
      EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin L)) (hα : α ≤ 1) :
    LittlePeriodicCAlphaFunction a M k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α →L[ℝ] LittlePeriodicCAlphaFunction a L k α := by
  let T := periodicCAlphaBilinearContinuous (a := a) (k := k) B hα
  have hcont : Continuous (fun z : PeriodicCAlphaFunction a M k α ×
      PeriodicCAlphaFunction a N k α ↦ T z.1 z.2) :=
    (T.continuous.comp continuous_fst).clm_apply continuous_snd
  have hmaps : MapsTo (fun z : PeriodicCAlphaFunction a M k α ×
      PeriodicCAlphaFunction a N k α ↦ T z.1 z.2)
      ((smoothPeriodicCAlphaSubmodule a M k α : Set (PeriodicCAlphaFunction a M k α)) ×ˢ
        (smoothPeriodicCAlphaSubmodule a N k α : Set (PeriodicCAlphaFunction a N k α)))
      (smoothPeriodicCAlphaSubmodule a L k α : Set (PeriodicCAlphaFunction a L k α)) := by
    intro z hz
    change ContDiff ℝ ∞ (fun x ↦ B (z.1.toFun x) (z.2.toFun x))
    exact (B.contDiff.comp (show ContDiff ℝ ∞ z.1.toFun from hz.1)).clm_apply
      (show ContDiff ℝ ∞ z.2.toFun from hz.2)
  have hclosure := hmaps.closure hcont
  have hmem (f : LittlePeriodicCAlphaFunction a M k α)
      (g : LittlePeriodicCAlphaFunction a N k α) :
      T f.val g.val ∈ (smoothPeriodicCAlphaSubmodule a L k α).topologicalClosure := by
    have hpair : (f.val, g.val) ∈ closure
        ((smoothPeriodicCAlphaSubmodule a M k α : Set (PeriodicCAlphaFunction a M k α)) ×ˢ
          (smoothPeriodicCAlphaSubmodule a N k α : Set (PeriodicCAlphaFunction a N k α))) := by
      rw [closure_prod_eq]
      exact ⟨f.property, g.property⟩
    exact hclosure hpair
  let Q (f : LittlePeriodicCAlphaFunction a M k α) (g : LittlePeriodicCAlphaFunction a N k α) :
      LittlePeriodicCAlphaFunction a L k α := ⟨T f.val g.val, hmem f g⟩
  let S : LittlePeriodicCAlphaFunction a M k α →ₗ[ℝ]
      LittlePeriodicCAlphaFunction a N k α →ₗ[ℝ] LittlePeriodicCAlphaFunction a L k α :=
    { toFun := fun f ↦
        { toFun := Q f
          map_add' := fun g₁ g₂ ↦ Subtype.ext ((T f.val).map_add g₁.val g₂.val)
          map_smul' := fun c g ↦ Subtype.ext ((T f.val).map_smul c g.val) }
      map_add' := by
        intro f₁ f₂
        apply LinearMap.ext
        intro g
        apply Subtype.ext
        exact congrArg (fun R ↦ R g.val) (T.map_add f₁.val f₂.val)
      map_smul' := by
        intro c f
        apply LinearMap.ext
        intro g
        apply Subtype.ext
        exact congrArg (fun R ↦ R g.val) (T.map_smul c f.val) }
  have hbound (f : LittlePeriodicCAlphaFunction a M k α)
      (g : LittlePeriodicCAlphaFunction a N k α) : ‖S f g‖ ≤ ‖T‖ * ‖f‖ * ‖g‖ := by
    change ‖T f.val g.val‖ ≤ ‖T‖ * ‖f.val‖ * ‖g.val‖
    exact ((T f.val).le_opNorm g.val).trans
      (mul_le_mul_of_nonneg_right (T.le_opNorm f.val) (norm_nonneg g.val))
  exact S.mkContinuous₂ ‖T‖ hbound

#print axioms littlePeriodicCAlphaBilinear

end GlobalEmbedding.Paper
