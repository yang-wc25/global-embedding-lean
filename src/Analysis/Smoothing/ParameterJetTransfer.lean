import Smoothing.ParameterSpatialTransitions
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Explicit source-two-jet transfer operators

These are actual linear maps on (value, first source derivative, second source
derivative). They use only the cutoff two-jet and the first two derivatives of
the source transition. The construction is independent of the map being smoothed.
-/

open GlobalEmbedding.Paper Function Filter Set ContinuousLinearMap
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation
noncomputable section

variable (Es Y : Type*) [NormedAddCommGroup Es] [NormedSpace ℝ Es]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The genuine value, source first derivative and source second derivative. -/
abbrev SpatialNativeJet := Y × ((Es →L[ℝ] Y) × (Es →L[ℝ] Es →L[ℝ] Y))

variable {Es Y}
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

/-- The actual spatial jet of one joint function, not independent fields. -/
def spatialNativeJet (u : Ep × Es → Y) (z : Ep × Es) : (Y × ((Es →L[ℝ] Y) × (Es →L[ℝ] Es →L[ℝ] Y))) :=
  (u z, fderiv ℝ (fun x => u (z.1,x)) z.2,
    fderiv ℝ (fderiv ℝ (fun x => u (z.1,x))) z.2)

theorem spatialNativeJet_contDiffOn {u : Ep × Es → Y} {O : Set (Ep × Es)}
    (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O) :
    ContDiffOn ℝ ∞ (spatialNativeJet u) O :=
  hu.prodMk ((incrementsJointSpatialJets_bridge u O hO hu).2.1.prodMk
    (incrementsJointSpatialJets_bridge u O hO hu).2.2)

variable [FiniteDimensional ℝ Es] [FiniteDimensional ℝ Y]

local instance spatialNativeJetNormedAddCommGroup : NormedAddCommGroup (SpatialNativeJet Es Y) :=
  inferInstanceAs (NormedAddCommGroup (Y × ((Es →L[ℝ] Y) × (Es →L[ℝ] Es →L[ℝ] Y))))
local instance spatialNativeJetNormedSpace : NormedSpace ℝ (SpatialNativeJet Es Y) :=
  inferInstanceAs (NormedSpace ℝ (Y × ((Es →L[ℝ] Y) × (Es →L[ℝ] Es →L[ℝ] Y))))


/-- Multiplication of the true spatial jet by a cutoff, with BOTH mixed
first-derivative terms and the cutoff Hessian term retained. -/
def spatialJetWeight (w₀ : ℝ) (w₁ : Es →L[ℝ] ℝ) (w₂ : Es →L[ℝ] Es →L[ℝ] ℝ) :
    (Y × ((Es →L[ℝ] Y) × (Es →L[ℝ] Es →L[ℝ] Y))) →L[ℝ] (Y × ((Es →L[ℝ] Y) × (Es →L[ℝ] Es →L[ℝ] Y))) :=
  LinearMap.toContinuousLinearMap
  { toFun := fun v =>
      (w₀ • v.1, w₁.smulRight v.1 + w₀ • v.2.1,
        ((ContinuousLinearMap.smulRightL ℝ Es Y).flip v.1).comp w₂ +
        w₁.smulRight v.2.1 + (w₁.smulRight v.2.1).flip + w₀ • v.2.2)
    map_add' := by
      intro v w
      ext <;> simp [smul_add, ContinuousLinearMap.smulRight_apply] <;> abel
    map_smul' := by
      intro c v
      ext <;> simp [smul_smul, ContinuousLinearMap.smulRight_apply, mul_comm] }



/-- The actual source chain rule as a linear map of input jets. -/
def spatialJetPullback (b₁ : Es →L[ℝ] Es) (b₂ : Es →L[ℝ] Es →L[ℝ] Es) :
    (Y × ((Es →L[ℝ] Y) × (Es →L[ℝ] Es →L[ℝ] Y))) →L[ℝ] (Y × ((Es →L[ℝ] Y) × (Es →L[ℝ] Es →L[ℝ] Y))) :=
  LinearMap.toContinuousLinearMap
  { toFun := fun v =>
      (v.1, v.2.1.comp b₁,
        (ContinuousLinearMap.compL ℝ Es Es Y v.2.1).comp b₂ +
        ((ContinuousLinearMap.compL ℝ Es Es Y).flip b₁).comp (v.2.2.comp b₁))
    map_add' := by intro v w; ext <;> simp; abel
    map_smul' := by intro c v; ext <;> simp }

/-- Weight and coordinate transfer, independent of the unknown map. -/
def spatialJetTransfer (w₀ : ℝ) (w₁ : Es →L[ℝ] ℝ) (w₂ : Es →L[ℝ] Es →L[ℝ] ℝ)
    (b₁ : Es →L[ℝ] Es) (b₂ : Es →L[ℝ] Es →L[ℝ] Es) :
    (Y × ((Es →L[ℝ] Y) × (Es →L[ℝ] Es →L[ℝ] Y))) →L[ℝ] (Y × ((Es →L[ℝ] Y) × (Es →L[ℝ] Es →L[ℝ] Y))) :=
  (spatialJetWeight w₀ w₁ w₂).comp (spatialJetPullback b₁ b₂)

section SmoothTransfer
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {O : Set Z}

/-- The explicit transfer coefficients depend smoothly on their genuine fields. -/
theorem spatialJetWeight_contDiffOn {w₀ : Z → ℝ} {w₁ : Z → Es →L[ℝ] ℝ}
    {w₂ : Z → Es →L[ℝ] Es →L[ℝ] ℝ}
    (h₀ : ContDiffOn ℝ ∞ w₀ O) (h₁ : ContDiffOn ℝ ∞ w₁ O)
    (h₂ : ContDiffOn ℝ ∞ w₂ O) :
    ContDiffOn ℝ ∞ (fun z => spatialJetWeight (Y := Y) (w₀ z) (w₁ z) (w₂ z)) O := by
  rw [contDiffOn_clm_apply]
  intro v
  change ContDiffOn ℝ ∞ (fun z => (w₀ z • v.1,
    (w₁ z).smulRight v.1 + w₀ z • v.2.1,
    ((ContinuousLinearMap.smulRightL ℝ Es Y).flip v.1).comp (w₂ z) +
      (w₁ z).smulRight v.2.1 + ((w₁ z).smulRight v.2.1).flip + w₀ z • v.2.2)) O
  have hv0 : ContDiffOn ℝ ∞ (fun z => w₀ z • v.1) O := h₀.smul contDiffOn_const
  have hv1 : ContDiffOn ℝ ∞ (fun z => (w₁ z).smulRight v.1 + w₀ z • v.2.1) O :=
    ((ContinuousLinearMap.smulRightL ℝ Es Y).contDiff.comp_contDiffOn h₁ |>.clm_apply
      contDiffOn_const).add (h₀.smul contDiffOn_const)
  have ha : ContDiffOn ℝ ∞ (fun z =>
      ((ContinuousLinearMap.smulRightL ℝ Es Y).flip v.1).comp (w₂ z)) O :=
    contDiffOn_const.clm_comp h₂
  have hb : ContDiffOn ℝ ∞ (fun z => (w₁ z).smulRight v.2.1) O := by
    rw [contDiffOn_clm_apply]
    intro a
    change ContDiffOn ℝ ∞ (fun z => w₁ z a • v.2.1) O
    exact (h₁.clm_apply contDiffOn_const).smul contDiffOn_const
  have hc : ContDiffOn ℝ ∞ (fun z => ((w₁ z).smulRight v.2.1).flip) O := by
    rw [contDiffOn_clm_apply]
    intro a
    rw [contDiffOn_clm_apply]
    intro b
    change ContDiffOn ℝ ∞ (fun z => w₁ z b • v.2.1 a) O
    exact (h₁.clm_apply contDiffOn_const).smul contDiffOn_const
  have hd : ContDiffOn ℝ ∞ (fun z => w₀ z • v.2.2) O := by
    rw [contDiffOn_clm_apply]
    intro a
    rw [contDiffOn_clm_apply]
    intro b
    change ContDiffOn ℝ ∞ (fun z => w₀ z • v.2.2 a b) O
    exact h₀.smul contDiffOn_const
  have hv2 := ((ha.add hb).add hc).add hd
  exact hv0.prodMk (hv1.prodMk hv2)

/-- Both terms in the actual source Hessian pullback vary smoothly. -/
theorem spatialJetPullback_contDiffOn {b₁ : Z → Es →L[ℝ] Es}
    {b₂ : Z → Es →L[ℝ] Es →L[ℝ] Es}
    (h₁ : ContDiffOn ℝ ∞ b₁ O) (h₂ : ContDiffOn ℝ ∞ b₂ O) :
    ContDiffOn ℝ ∞ (fun z => spatialJetPullback (Y := Y) (b₁ z) (b₂ z)) O := by
  rw [contDiffOn_clm_apply]
  intro v
  change ContDiffOn ℝ ∞ (fun z => (v.1, v.2.1.comp (b₁ z),
    (ContinuousLinearMap.compL ℝ Es Es Y v.2.1).comp (b₂ z) +
    ((ContinuousLinearMap.compL ℝ Es Es Y).flip (b₁ z)).comp (v.2.2.comp (b₁ z)))) O
  have hv0 : ContDiffOn ℝ ∞ (fun _ : Z => v.1) O := contDiffOn_const
  have hv1 : ContDiffOn ℝ ∞ (fun z => v.2.1.comp (b₁ z)) O := contDiffOn_const.clm_comp h₁
  have ha : ContDiffOn ℝ ∞ (fun z =>
      (ContinuousLinearMap.compL ℝ Es Es Y v.2.1).comp (b₂ z)) O :=
    contDiffOn_const.clm_comp h₂
  have hb : ContDiffOn ℝ ∞ (fun z =>
      (ContinuousLinearMap.compL ℝ Es Es Y).flip (b₁ z)) O := by
    rw [contDiffOn_clm_apply]
    intro L
    change ContDiffOn ℝ ∞ (fun z => L.comp (b₁ z)) O
    exact contDiffOn_const.clm_comp h₁
  have hc : ContDiffOn ℝ ∞ (fun z => v.2.2.comp (b₁ z)) O :=
    contDiffOn_const.clm_comp h₁
  exact hv0.prodMk (hv1.prodMk (ha.add (hb.clm_comp hc)))

#print axioms spatialJetWeight_contDiffOn
#print axioms spatialJetPullback_contDiffOn

end SmoothTransfer

end
end GlobalEmbedding.Continuation
