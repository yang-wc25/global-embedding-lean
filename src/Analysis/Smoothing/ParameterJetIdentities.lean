import Smoothing.ParameterJetTransfer

/-!
# Spatial jet transfer is the derivative of the actual localized map

The formulas here connect the explicit linear operators to native derivatives.
Both cutoff cross terms and the Hessian of the spatial chart transition occur.
-/

open GlobalEmbedding.Paper Function Filter Set ContinuousLinearMap
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
noncomputable section

variable {Es Y : Type*} [NormedAddCommGroup Es] [NormedSpace ℝ Es]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Exact second derivative of a scalar times a vector-valued function. -/
theorem parameter_second_fderiv_smul {a : Es → ℝ} {f : Es → Y}
    {O : Set Es} (hO : IsOpen O) (ha : ContDiffOn ℝ ∞ a O)
    (hf : ContDiffOn ℝ ∞ f O) {x : Es} (hx : x ∈ O) (v w : Es) :
    fderiv ℝ (fderiv ℝ (fun y => a y • f y)) x v w =
      fderiv ℝ (fderiv ℝ a) x v w • f x +
      fderiv ℝ a x v • fderiv ℝ f x w +
      fderiv ℝ a x w • fderiv ℝ f x v +
      a x • fderiv ℝ (fderiv ℝ f) x v w := by
  have ha0 := (ha.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hf0 := (hf.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have had := ha.fderiv_of_isOpen hO (m := ∞) (by simp)
  have hfd := hf.fderiv_of_isOpen hO (m := ∞) (by simp)
  have ha1 := (had.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hf1 := (hfd.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have heq : fderiv ℝ (fun y => a y • f y) =ᶠ[𝓝 x]
      (fun y => a y • fderiv ℝ f y + (fderiv ℝ a y).smulRight (f y)) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact ((ha.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp) |>.hasFDerivAt.smul
      ((hf.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt).fderiv
  rw [heq.fderiv_eq]
  have hleft := ha0.hasFDerivAt.smul hf1.hasFDerivAt
  have hright := (ContinuousLinearMap.smulRightL ℝ Es Y).hasFDerivAt_of_bilinear
    ha1.hasFDerivAt hf0.hasFDerivAt
  have hh := (hleft.add hright).fderiv
  have hv := congrArg (fun L => L v w) hh
  simp only [ContinuousLinearMap.smulRightL_apply_apply] at hv
  refine hv.trans ?_
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.compL_apply]
  abel

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [FiniteDimensional ℝ Es] [FiniteDimensional ℝ Y]

attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

/-- The explicit cutoff operator is exactly the true spatial jet of w*u. -/
theorem spatialNativeJet_weight {w : Ep × Es → ℝ} {u : Ep × Es → Y}
    {O : Set (Ep × Es)} (hO : IsOpen O) (hw : ContDiffOn ℝ ∞ w O)
    (hu : ContDiffOn ℝ ∞ u O) {z : Ep × Es} (hz : z ∈ O) :
    spatialNativeJet (fun y => w y • u y) z =
      spatialJetWeight (w z) (fderiv ℝ (fun x => w (z.1,x)) z.2)
        (fderiv ℝ (fderiv ℝ (fun x => w (z.1,x))) z.2) (spatialNativeJet u z) := by
  let Os := (fun x : Es => (z.1,x)) ⁻¹' O
  have hOs : IsOpen Os := hO.preimage (continuous_const.prodMk continuous_id)
  have hws : ContDiffOn ℝ ∞ (fun x : Es => w (z.1,x)) Os :=
    hw.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ h => h)
  have hus : ContDiffOn ℝ ∞ (fun x : Es => u (z.1,x)) Os :=
    hu.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ h => h)
  apply Prod.ext
  · rfl
  apply Prod.ext
  · change fderiv ℝ (fun x => w (z.1,x) • u (z.1,x)) z.2 = _
    rw [fderiv_fun_smul ((hws.contDiffAt (hOs.mem_nhds hz)).differentiableAt (by simp))
      ((hus.contDiffAt (hOs.mem_nhds hz)).differentiableAt (by simp))]
    exact add_comm _ _
  · apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro v'
    exact parameter_second_fderiv_smul hOs hws hus hz v v'

/-- The explicit pullback operator is exactly the true spatial jet through
a product transition, on any original open source/parameter overlap. -/
theorem spatialNativeJet_pullback
    (a : Ep → Ep) {b : Es → Es} {u : Ep × Es → Y}
    {Op : Set Ep} {Os : Set Es} {V : Set (Ep × Es)}
    (hOs : IsOpen Os) (hV : IsOpen V) (hu : ContDiffOn ℝ ∞ u V)
    (hb : ContDiffOn ℝ ∞ b Os) (hmap : ∀ p ∈ Op, ∀ x ∈ Os, (a p,b x) ∈ V)
    {z : Ep × Es} (hz : z ∈ Op ×ˢ Os) :
    spatialNativeJet (fun y => u (a y.1,b y.2)) z =
      spatialJetPullback (fderiv ℝ b z.2) (fderiv ℝ (fderiv ℝ b) z.2)
        (spatialNativeJet u (a z.1,b z.2)) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · exact parameter_product_spatial_first a hOs hV hu hb z.1 (hmap z.1 hz.1) hz.2
  · apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact parameter_product_spatial_second a hOs hV hu hb z.1 (hmap z.1 hz.1) hz.2 v w

/-- The actual geometric coefficient field for a localized product transition. -/
def spatialTransferField (w : Ep × Es → ℝ) (b : Es → Es) (z : Ep × Es) :
    SpatialNativeJet Es Y →L[ℝ] SpatialNativeJet Es Y :=
  spatialJetTransfer (w z) (fderiv ℝ (fun x => w (z.1,x)) z.2)
    (fderiv ℝ (fderiv ℝ (fun x => w (z.1,x))) z.2)
    (fderiv ℝ b z.2) (fderiv ℝ (fderiv ℝ b) z.2)

/-- This is the true coefficient field, whose derivatives are geometric data. -/
theorem spatialTransferField_contDiffOn {w : Ep × Es → ℝ} {b : Es → Es}
    {Op : Set Ep} {Os : Set Es} (hOp : IsOpen Op) (hOs : IsOpen Os)
    (hw : ContDiffOn ℝ ∞ w (Op ×ˢ Os)) (hb : ContDiffOn ℝ ∞ b Os) :
    ContDiffOn ℝ ∞ (spatialTransferField (Y := Y) w b) (Op ×ˢ Os) := by
  have hwj := incrementsJointSpatialJets_bridge w (Op ×ˢ Os) (hOp.prod hOs) hw
  have hb₁ := hb.fderiv_of_isOpen hOs (m := ∞) (by simp)
  have hb₂ := hb₁.fderiv_of_isOpen hOs (m := ∞) (by simp)
  exact (spatialJetWeight_contDiffOn hw hwj.2.1 hwj.2.2).clm_comp
    (spatialJetPullback_contDiffOn
      (hb₁.comp contDiffOn_snd (fun _ h => h.2))
      (hb₂.comp contDiffOn_snd (fun _ h => h.2)))

/-- Exact source-two-jet transfer for the same localized map. -/
theorem spatialNativeJet_transfer {w : Ep × Es → ℝ}
    {a : Ep → Ep} {b : Es → Es} {u : Ep × Es → Y}
    {Op : Set Ep} {Os : Set Es} {V : Set (Ep × Es)}
    (hOp : IsOpen Op) (hOs : IsOpen Os) (hV : IsOpen V)
    (hw : ContDiffOn ℝ ∞ w (Op ×ˢ Os)) (hu : ContDiffOn ℝ ∞ u V)
    (ha : ContDiffOn ℝ ∞ a Op) (hb : ContDiffOn ℝ ∞ b Os)
    (hmap : ∀ p ∈ Op, ∀ x ∈ Os, (a p,b x) ∈ V)
    {z : Ep × Es} (hz : z ∈ Op ×ˢ Os) :
    spatialNativeJet (fun y => w y • u (a y.1,b y.2)) z =
      spatialTransferField w b z (spatialNativeJet u (a z.1,b z.2)) := by
  have ht : ContDiffOn ℝ ∞ (fun y : Ep × Es => (a y.1,b y.2)) (Op ×ˢ Os) :=
    (ha.comp contDiffOn_fst (fun _ h => h.1)).prodMk
      (hb.comp contDiffOn_snd (fun _ h => h.2))
  have hh := spatialNativeJet_weight (hOp.prod hOs) hw
    (hu.comp ht (fun y hy => hmap y.1 hy.1 y.2 hy.2)) hz
  simp only [Function.comp_def] at hh
  rw [hh, spatialNativeJet_pullback a hOs hV hu hb hmap hz]
  rfl

#print axioms spatialTransferField_contDiffOn
#print axioms spatialNativeJet_transfer

#print axioms parameter_second_fderiv_smul
#print axioms spatialNativeJet_weight
#print axioms spatialNativeJet_pullback

end
end GlobalEmbedding.Continuation
