import NormalPolar.ParameterDisplacementPrescribedRaw
import Probes.ActualSecondaryQuadraticConstruction

/-!
# Reuse actual unit-scale geometry for prescribed amplitudes

This internal adapter keeps the actual geometry, chart and carrier. A
unit-scale geometry sample equal to the whole chart target supplies the
prescribed whole-target second-form-row bounds. Taking both source orders
to `max n j` and using `ell^k <= 1` loses no small-scale factor.

The general-wave producer manufactures this geometry and the primitive
profiles before invoking the adapter; they are not added to its public
original-input assumptions.
-/

noncomputable section
open Set Function Manifold
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical

namespace GlobalEmbedding.Continuation

private theorem generalPrescribed_weighted_norm_le {Y : Type*}
    [NormedAddCommGroup Y] (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (k : ℕ) (v : Y) (C : ℝ) (h : ‖v‖ ≤ C) : ell^k * ‖v‖ ≤ C :=
  ((mul_le_mul_of_nonneg_right (pow_le_one₀ he he1) (norm_nonneg v)).trans_eq
    (one_mul _)).trans h

variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D

/-- An exact adapter from the already constructed geometry. The constants
do not get divided by `ell`; all coefficient norms are bounded at unit scale. -/
def generalPrescribedRawOfUnitGeometry
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c b x))
    (a : OpenPartialHomeomorph (Ep × M) X) (W K : Set (Ep × M))
    (n j : ℕ) (ell Mg Bchi Bnu : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (g : ActualSecondaryRawGeometry F hF (max n j) (max n j) 1 Mg W)
    (hc : g.c = c) (ha : g.chart = a) (hs : g.sample = a.target) (hK : g.support = K)
    (hcut : ∀ z ∈ a.target, z ∈ tsupport chi → a.symm z ∈ K)
    (hchi : ContDiffOn ℝ ∞ chi a.target)
    (hnu : ContDiffOn ℝ ∞ (fun z : X => (nu z.1 z.2 : V)) a.target)
    (bchi : ∀ k ≤ n, ∀ z ∈ a.target,
      ell^k * ‖iteratedFDeriv ℝ k chi z‖ ≤ Bchi)
    (bnu : ∀ k ≤ n, ∀ z ∈ a.target,
      ell^k * ‖iteratedFDeriv ℝ k (fun y : X => (nu y.1 y.2 : V)) z‖ ≤ Bnu) :
    ActualPrescribedSpatialRawProfiles F hF c chi nu a W K n j ell Mg Bchi Bnu := by
  subst c
  refine {
    sample := a.target
    sample_subset := Subset.rfl
    closed_support := by simpa only [hK] using g.support_closed
    support_source := by simpa only [hK,ha] using g.support_source
    chart_smooth := by simpa only [ha] using g.chart_smooth
    cutoff_support := hcut
    A_smooth := by simpa only [ha] using g.coefficientA_smooth
    B_smooth := by simpa only [ha] using g.coefficientB_smooth
    G_smooth := by simpa only [ha] using g.inverse_smooth
    J_smooth := by simpa only [ha] using g.transverse_smooth
    T_smooth := by simpa only [ha] using g.value_smooth
    BR_smooth := by simpa only [ha] using g.brows_smooth
    cutoff_smooth := hchi
    normal_smooth := hnu
    A_jets := by
      intro k hk z hz
      apply generalPrescribed_weighted_norm_le ell he he1
      have hb := g.coefficientA_bound k (hk.trans (le_max_left _ _)) z (by rwa [hs])
      simpa only [one_pow,one_mul] using hb
    B_jets := by
      intro k hk z hz
      apply generalPrescribed_weighted_norm_le ell he he1
      have hb := g.coefficientB_bound k (hk.trans (le_max_left _ _)) z (by rwa [hs])
      simpa only [one_pow,one_mul] using hb
    G_jets := by
      intro k hk z hz
      apply generalPrescribed_weighted_norm_le ell he he1
      have hb := g.inverse_bound k (hk.trans (le_max_right _ _)) z (by rwa [hs])
      simpa only [one_pow,one_mul] using hb
    J_jets := by
      intro k hk z hz
      apply generalPrescribed_weighted_norm_le ell he he1
      have hb := g.transverse_bound k (hk.trans (le_max_right _ _)) z (by rwa [hs])
      simpa only [one_pow,one_mul] using hb
    T_jets := by
      intro k hk z hz
      apply generalPrescribed_weighted_norm_le ell he he1
      have hb := g.value_bound k (hk.trans (le_max_right _ _)) z (by rwa [hs])
      simpa only [one_pow,one_mul] using hb
    BR_jets := by
      intro k hk z hz
      apply generalPrescribed_weighted_norm_le ell he he1
      have hb := g.brows_bound k (hk.trans (le_max_left _ _)) z (by rwa [hs])
      simpa only [one_pow,one_mul] using hb
    cutoff_jets := bchi
    normal_jets := bnu }

theorem generalPrescribedRawOfUnitGeometry_sample
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c b x))
    (a : OpenPartialHomeomorph (Ep × M) X) (W K : Set (Ep × M))
    (n j : ℕ) (ell Mg Bchi Bnu : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (g : ActualSecondaryRawGeometry F hF (max n j) (max n j) 1 Mg W)
    (hc : g.c = c) (ha : g.chart = a) (hs : g.sample = a.target) (hK : g.support = K)
    (hcut : ∀ z ∈ a.target, z ∈ tsupport chi → a.symm z ∈ K)
    (hchi : ContDiffOn ℝ ∞ chi a.target)
    (hnu : ContDiffOn ℝ ∞ (fun z : X => (nu z.1 z.2 : V)) a.target)
    (bchi : ∀ k ≤ n, ∀ z ∈ a.target,
      ell^k * ‖iteratedFDeriv ℝ k chi z‖ ≤ Bchi)
    (bnu : ∀ k ≤ n, ∀ z ∈ a.target,
      ell^k * ‖iteratedFDeriv ℝ k (fun y : X => (nu y.1 y.2 : V)) z‖ ≤ Bnu) :
    (generalPrescribedRawOfUnitGeometry F hF c chi nu a W K n j ell Mg Bchi Bnu
      he he1 g hc ha hs hK hcut hchi hnu bchi bnu).sample = a.target := by
  subst c
  rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.generalPrescribedRawOfUnitGeometry
#print axioms GlobalEmbedding.Continuation.generalPrescribedRawOfUnitGeometry_sample
