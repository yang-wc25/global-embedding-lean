import NormalPolar.ActualRepairModelCentered
import NormalPolar.ActualProbeFirstSpatial
import Smoothing.ParameterOriginalCoreBounds

/-!
# Original spatial bounds of the same complete first increment

The original weighted order-two norm contains its order-three term with
coefficient tau. Extracting that term gives the delta/tau² bound needed
for a uniform spatial C³ bound after the paper's scale substitution.
The centered slice comparison has constant one and uses the same original
source samples and full parameter ball. The actual reference contraction
is retained when passing to the complete first map.

These results consume the numerical bounds of the actual increment. They
do not identify a separately chosen map or a closed-state budget with it.
-/

noncomputable section
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

/-- The first two relevant terms of the original weighted norm. The scale
is positive, so its order-three coefficient can be cancelled even in the
extended nonnegative reals. No finiteness of an unbounded derivative is
silently assumed. -/
theorem probes_weighted_two_controls_three
    {ι : Type*} [Fintype ι] {a N q : ℕ}
    (f : ι → (Fin a → ℝ) → Fin N → ℝ)
    (O S : ι → Set (Fin a → ℝ))
    (tau delta C : ℝ) (htau : 0 < tau) (hq : 1 ≤ q)
    (hfinite : paperAtlasWeighted 2 q tau f O S ≠ ⊤)
    (hbound : (paperAtlasWeighted 2 q tau f O S).toReal ≤ C*delta/tau) :
    paperAtlasCj 2 f O S ≤ ENNReal.ofReal (C*delta/tau) ∧
    paperAtlasCj 3 f O S ≤ ENNReal.ofReal (C*delta/tau^2) := by
  have hw : paperAtlasWeighted 2 q tau f O S ≤ ENNReal.ofReal (C*delta/tau) := by
    simpa only [ENNReal.ofReal_toReal hfinite] using ENNReal.ofReal_le_ofReal hbound
  refine ⟨(parameterPaperAtlasCj_base_le_weighted 2 q tau f O S).trans hw,?_⟩
  have hterm : ENNReal.ofReal tau * paperAtlasCj 3 f O S ≤
      paperAtlasWeighted 2 q tau f O S := by
    have h := Finset.single_le_sum (s := Finset.range (q+1))
      (f := fun k => ENNReal.ofReal tau ^ k * paperAtlasCj (k+2) f O S)
      (fun k _ => bot_le) (show 1 ∈ Finset.range (q+1) by simp; omega)
    simpa only [paperAtlasWeighted,pow_one] using h
  apply (ENNReal.mul_le_mul_iff_right
    (ne_of_gt (ENNReal.ofReal_pos.mpr htau)) ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal tau * paperAtlasCj 3 f O S ≤
        ENNReal.ofReal (C*delta/tau) := hterm.trans hw
    _ = ENNReal.ofReal tau * ENNReal.ofReal (C*delta/tau^2) := by
      rw [← ENNReal.ofReal_mul htau.le]
      congr 1
      field_simp [htau.ne']

variable {n d N c : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)

private local instance : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
private local instance : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

/-- Every point of the same centered ball inherits both spatial budgets
from the same original order-two weighted norm. In particular no ball
shrink or replacement of the original atlas gauge occurs. -/
theorem probes_original_centered_increment_spatial
    (A : BufferedAtlas M Es) (hA : IsSmoothBufferedAtlas A)
    (B : TensorBufferedChartFamily (Fin c) P Ep)
    (hB : ∀ b, B.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQ : ∀ b, Q b ⊆ (B.chart b).target)
    (hQsampling : ∀ b, tensorLocalSamplingCoordinates B b ⊆ Q b)
    (U : P × M → V) (hU : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,V) ∞ U)
    (b : Fin c) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (u : Fin d → ℝ) (hu : ‖u‖ < actualRepairParameterRadius B)
    (tau delta C : ℝ) (htau : 0 < tau)
    (hfinite : paperAtlasWeighted 2 440 tau
      (incrementsOriginalMapCoordinates A B.chart U)
      (incrementsOriginalDifferentiation A B.chart)
      (incrementsOriginalEvaluation A B.chart Omega Q univ) ≠ ⊤)
    (hbound : (paperAtlasWeighted 2 440 tau
      (incrementsOriginalMapCoordinates A B.chart U)
      (incrementsOriginalDifferentiation A B.chart)
      (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal ≤ C*delta/tau) :
    probeAtlasCj (actualRepairSamplingAtlas A Omega) 2
      (fun x => U (actualRepairParameterMap B b p₀ u,x)) ≤ ENNReal.ofReal (C*delta/tau) ∧
    probeAtlasCj (actualRepairSamplingAtlas A Omega) 3
      (fun x => U (actualRepairParameterMap B b p₀ u,x)) ≤ ENNReal.ofReal (C*delta/tau^2) := by
  have htotal := probes_weighted_two_controls_three
    (incrementsOriginalMapCoordinates A B.chart U)
    (incrementsOriginalDifferentiation A B.chart)
    (incrementsOriginalEvaluation A B.chart Omega Q univ)
    tau delta C htau (by norm_num : 1 ≤ 440) hfinite hbound
  exact ⟨(actualRepairModel_centered_spatial_le_total A hA B hB Omega Q
      hOmega hQ hQsampling U hU b p₀ hp₀ u hu 2).trans htotal.1,
    (actualRepairModel_centered_spatial_le_total A hA B hB Omega Q
      hOmega hQ hQsampling U hU b p₀ hp₀ u hu 3).trans htotal.2⟩

/-- The same complete first map has the original C² closeness and uniform
C³ bounds at the paper scales. The constant depends on the fixed reference,
fixed threshold and increment constant, and is independent of t and u. -/
theorem probes_original_centered_first_spatial
    (A : BufferedAtlas M Es) (hA : IsSmoothBufferedAtlas A)
    (B : TensorBufferedChartFamily (Fin c) P Ep)
    (hB : ∀ b, B.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, Omega i ⊆ (A.chart i).target)
    (hOmegaCompact : ∀ i, IsCompact (Omega i))
    (hQ : ∀ b, Q b ⊆ (B.chart b).target)
    (hQsampling : ∀ b, tensorLocalSamplingCoordinates B b ⊆ Q b)
    (F₀ : M → V) (hF₀ : ContMDiff 𝓘(ℝ,Es) 𝓘(ℝ,V) ∞ F₀)
    (U : P × M → V) (hU : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,V) ∞ U)
    (b : Fin c) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (u : Fin d → ℝ) (hu : ‖u‖ < actualRepairParameterRadius B)
    (threshold C t : ℝ) (hC : 0 ≤ C) (ht : 0 < t) (htt : t < threshold)
    (hfinite : paperAtlasWeighted 2 440 (t^((6:ℝ)/5))
      (incrementsOriginalMapCoordinates A B.chart U)
      (incrementsOriginalDifferentiation A B.chart)
      (incrementsOriginalEvaluation A B.chart Omega Q univ) ≠ ⊤)
    (hbound : (paperAtlasWeighted 2 440 (t^((6:ℝ)/5))
      (incrementsOriginalMapCoordinates A B.chart U)
      (incrementsOriginalDifferentiation A B.chart)
      (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal ≤ C*t^(10:ℕ)/t^((6:ℝ)/5)) :
    let Aout := actualRepairSamplingAtlas A Omega
    let hAout := actualRepairSamplingAtlas_smooth A hA Omega hOmega
    let hcompact := actualRepairSamplingAtlas_support_compact A Omega hOmegaCompact hOmega
    let Cfirst := actualProbeFirstSpatialConstant Aout hAout hcompact F₀ hF₀ threshold C C
    let G := fun x => Real.sqrt (1-(t^(10:ℕ))^2) • F₀ x +
      U (actualRepairParameterMap B b p₀ u,x)
    0 ≤ Cfirst ∧ probeAtlasCj Aout 2 (G-F₀) ≤ ENNReal.ofReal (Cfirst*t^((44:ℝ)/5)) ∧
      probeAtlasCj Aout 3 G ≤ ENNReal.ofReal Cfirst := by
  intro Aout hAout hcompact Cfirst G
  have hinc := probes_original_centered_increment_spatial A hA B hB Omega Q
    hOmega hQ hQsampling U hU b p₀ hp₀ u hu
    (t^((6:ℝ)/5)) (t^(10:ℕ)) C (Real.rpow_pos_of_pos ht _) hfinite hbound
  have hslice : ContMDiff 𝓘(ℝ,Es) 𝓘(ℝ,V) ∞
      (fun x => U (actualRepairParameterMap B b p₀ u,x)) := by
    apply hU.comp
    rw [modelWithCornersSelf_prod]
    exact contMDiff_const.prodMk contMDiff_id
  exact ⟨actualProbeFirstSpatialConstant_nonneg Aout hAout hcompact F₀ hF₀ threshold C C hC hC,
    actual_probe_first_spatial_budgets Aout hAout hcompact F₀ hF₀
      (fun x => U (actualRepairParameterMap B b p₀ u,x)) hslice
      threshold C C t hC hC ht htt hinc.1 hinc.2⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.probes_weighted_two_controls_three
#print axioms GlobalEmbedding.Continuation.probes_original_centered_increment_spatial
#print axioms GlobalEmbedding.Continuation.probes_original_centered_first_spatial
