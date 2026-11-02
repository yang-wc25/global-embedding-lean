import Smoothing.ParameterGeometryJets
import Mathlib.Topology.Order.Compact

/-!
# One fixed universal spatial-transfer model and its uniform derivative bounds

The compact set here belongs to the fixed finite-dimensional coefficient model,
not to any atlas. Its radius is later supplied by B(0..2), T(1..2). Thus the
chosen derivative bound is fixed before manifold, charts, scales, or map data.
Zero-dimensional models are included; no norm-one basis premise occurs.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Filter Set
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable (Es : Type*) [NormedAddCommGroup Es] [NormedSpace ℝ Es]

/-- Only geometric data: cutoff spatial two-jet and transition spatial Jacobian/Hessian. -/
abbrev SpatialTransferInput := SpatialNativeJet Es ℝ × ((Es →L[ℝ] Es) × (Es →L[ℝ] Es →L[ℝ] Es))

variable {Es} [FiniteDimensional ℝ Es]
variable (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

local instance spatialTransferInputNormedAddCommGroup : NormedAddCommGroup (SpatialTransferInput Es) :=
  inferInstanceAs (NormedAddCommGroup (SpatialNativeJet Es ℝ × ((Es →L[ℝ] Es) × (Es →L[ℝ] Es →L[ℝ] Es))))
local instance spatialTransferInputNormedSpace : NormedSpace ℝ (SpatialTransferInput Es) :=
  inferInstanceAs (NormedSpace ℝ (SpatialNativeJet Es ℝ × ((Es →L[ℝ] Es) × (Es →L[ℝ] Es →L[ℝ] Es))))

/-- The same explicit cutoff and source-transition polynomial for every chart. -/
def spatialTransferModel (v : SpatialTransferInput Es) : SpatialNativeJet Es Y →L[ℝ] SpatialNativeJet Es Y :=
  spatialJetTransfer v.1.1 v.1.2.1 v.1.2.2 v.2.1 v.2.2

/-- The universal coefficient model is genuinely smooth, proved from its formula. -/
theorem spatialTransferModel_contDiff : ContDiff ℝ ∞ (spatialTransferModel (Es := Es) Y) := by
  apply contDiffOn_univ.mp
  have hid : ContDiffOn ℝ ∞ (fun v : SpatialTransferInput Es => v) univ := contDiffOn_id
  have h0 : ContDiffOn ℝ ∞ (fun v : SpatialTransferInput Es => v.1.1) univ := hid.fst.fst
  have h1 : ContDiffOn ℝ ∞ (fun v : SpatialTransferInput Es => v.1.2.1) univ := hid.fst.snd.fst
  have h2 : ContDiffOn ℝ ∞ (fun v : SpatialTransferInput Es => v.1.2.2) univ := hid.fst.snd.snd
  have hb1 : ContDiffOn ℝ ∞ (fun v : SpatialTransferInput Es => v.2.1) univ := hid.snd.fst
  have hb2 : ContDiffOn ℝ ∞ (fun v : SpatialTransferInput Es => v.2.2) univ := hid.snd.snd
  exact (spatialJetWeight_contDiffOn h0 h1 h2).clm_comp (spatialJetPullback_contDiffOn hb1 hb2)

/-- A fixed model-only cumulative compact derivative bound. The maximum with
zero makes all signs valid even for empty balls, and also in zero dimension. -/
def spatialTransferModelBound (R : ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j+1), max 0 (sSup ((fun v : SpatialTransferInput Es =>
    ‖iteratedFDeriv ℝ k (spatialTransferModel (Es := Es) Y) v‖) '' Metric.closedBall 0 R))

theorem spatialTransferModelBound_nonneg (R : ℝ) (j : ℕ) :
    0 ≤ spatialTransferModelBound (Es := Es) Y R j :=
  Finset.sum_nonneg (fun _ _ => le_max_left _ _)

/-- Every actual universal-model derivative on the fixed ball is bounded by
the same predeclared quantity; compactness is used only on this model ball. -/
theorem spatialTransferModel_jet_le (R : ℝ) (j k : ℕ) (hk : k ≤ j)
    {v : SpatialTransferInput Es} (hv : ‖v‖ ≤ R) :
    ‖iteratedFDeriv ℝ k (spatialTransferModel (Es := Es) Y) v‖ ≤ spatialTransferModelBound (Es := Es) Y R j := by
  have hcompact : IsCompact (Metric.closedBall (0 : SpatialTransferInput Es) R) := isCompact_closedBall _ _
  have hcontinuous : Continuous (fun v : SpatialTransferInput Es =>
      ‖iteratedFDeriv ℝ k (spatialTransferModel (Es := Es) Y) v‖) :=
    ((spatialTransferModel_contDiff (Es := Es) Y).continuous_iteratedFDeriv (by simp)).norm
  have hsup : ‖iteratedFDeriv ℝ k (spatialTransferModel (Es := Es) Y) v‖ ≤
      sSup ((fun w : SpatialTransferInput Es => ‖iteratedFDeriv ℝ k (spatialTransferModel (Es := Es) Y) w‖) ''
        Metric.closedBall 0 R) :=
    le_csSup (hcompact.bddAbove_image hcontinuous.continuousOn)
      ⟨v, by simpa using hv, rfl⟩
  apply (hsup.trans (le_max_right 0 _)).trans
  unfold spatialTransferModelBound
  exact Finset.single_le_sum
    (f := fun a : ℕ => max (0 : ℝ) (sSup ((fun v : SpatialTransferInput Es =>
      ‖iteratedFDeriv ℝ a (spatialTransferModel (Es := Es) Y) v‖) '' Metric.closedBall 0 R)))
    (fun a _ => le_max_left (0 : ℝ) _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

section GeneralComposition
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Native composition with a possibly different fixed intermediate model. -/
theorem parameter_general_composition_jet_le (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    {f : E → F} {g : F → G} {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo f U V)
    {x : E} (hx : x ∈ U) (j : ℕ) (R : ℝ)
    (houter : ∀ k ≤ j, ‖iteratedFDeriv ℝ k g (f x)‖ ≤ R)
    (hinner : ∀ k, 1 ≤ k → k ≤ j → ‖iteratedFDeriv ℝ k f x‖ ≤ T k) :
    ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤
      (j.factorial : ℝ) * R * bufferedTransitionPrefix T j ^ j := by
  have hQ := one_le_bufferedTransitionPrefix hT j
  have hin (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) :
      ‖iteratedFDerivWithin ℝ k f U x‖ ≤ bufferedTransitionPrefix T j ^ k := by
    rw [iteratedFDerivWithin_of_isOpen k hU hx]
    have hsum : T k ≤ ∑ l ∈ Finset.range (j+1), T l :=
      Finset.single_le_sum (fun l _ => hT l) (by simpa using hkj)
    have hTQ : T k ≤ bufferedTransitionPrefix T j := by unfold bufferedTransitionPrefix; linarith
    exact (hinner k hk hkj).trans (hTQ.trans (le_self_pow₀ hQ (by omega)))
  have hout (k : ℕ) (hk : k ≤ j) : ‖iteratedFDerivWithin ℝ k g V (f x)‖ ≤ R := by
    rw [iteratedFDerivWithin_of_isOpen k hV (hmap hx)]
    exact houter k hk
  have h := norm_iteratedFDerivWithin_comp_le hg hf (n := j) (by simp)
    hV.uniqueDiffOn hU.uniqueDiffOn hmap hx hout hin
  rwa [iteratedFDerivWithin_of_isOpen j hU hx] at h
end GeneralComposition

#print axioms spatialTransferModel_contDiff
#print axioms spatialTransferModel_jet_le
#print axioms parameter_general_composition_jet_le
end
end GlobalEmbedding.Continuation
