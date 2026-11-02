import Probes.ActualSecondaryFamily
import Probes.ActualSecondaryResidualRegularity
import Probes.ActualIncrementSecondaryPhysicalTensor

/-!
# The physical residual of the same actual secondary family

The original finite algebra and all physical metric entries are identified on
the joint parameter/source open set. The chosen chart may vary with the
parameter. Every occurrence uses that same chart, source, finite polynomial,
full reconstruction and literal exponential displacement. The quantitative
joint jet transfer is kept separate from this exact geometric identity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Manifold Set Filter GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Source" => Fin (m + 1) → Fin (m + 1) → ℝ
local notation "Cdata" => Fin (m + 1) → ℂ

def actualSecondaryReducedResidual
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source) (tau : ℝ) (length : ℕ) : X → Cdata :=
  let U := actualSecondarySolution F hF c hR hI tau length
  fun z => ((tau : ℂ) / Complex.I)⁻¹ • U z.1 z.2 +
    incrementsModeComplexReducedOperator (F z.1) (hF z.1) (c z.1) (U z.1) z.2 -
      actualSecondaryComplexSource F hF c hR hI z

def actualSecondaryPhysicalError
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (chart : Ep → OpenPartialHomeomorph M D) (hR hI : X → Source)
    (tau : ℝ) (length : ℕ) : X → Fin (m + 1) → Fin (m + 1) → ℂ :=
  fun z =>
  let c := (chart z.1).symm
  let alpha := (tau : ℂ) / Complex.I
  let A := incrementsModeComplexFirstOrderA (F z.1) (hF z.1) c
  let B := incrementsModeComplexFirstOrderB (F z.1) (hF z.1) c
  let k := fun x => incrementsModeComplexInclude
    (incrementsModeSource (F z.1) (hF z.1) c (fun y => hR (z.1, y)) (fun _ => 0) x) +
    Complex.I • incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) c (fun y => hI (z.1, y)) (fun _ => 0) x)
  let U := incrementsActualModeSum A B alpha length k
  let ZR := incrementsModeFullReconstruction (F z.1) (hF z.1) c
    (fun x => incrementsModeRealPart (U x)) (fun y => hR (z.1, y)) (fun _ => 0)
  let ZI := incrementsModeFullReconstruction (F z.1) (hF z.1) c
    (fun x => incrementsModeImagPart (U x)) (fun y => hI (z.1, y)) (fun _ => 0)
  let WR := fun x => WithLp.toLp 2 (fun a : Fin N =>
    (Complex.exp (((x 0 / tau : ℝ) : ℂ) * Complex.I) *
      ((ZR x a : ℂ) + Complex.I * (ZI x a : ℂ))).re)
  let WI := fun x => WithLp.toLp 2 (fun a : Fin N =>
    (Complex.exp (((x 0 / tau : ℝ) : ℂ) * Complex.I) *
      ((ZR x a : ℂ) + Complex.I * (ZI x a : ℂ))).im)
  fun i j => Complex.exp (-((z.2 0 / tau : ℝ) : ℂ) * Complex.I) *
    ((incrementsCoordinateMetricVariation (F z.1 ∘ c) WR z.2
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ) + Complex.I *
      (incrementsCoordinateMetricVariation (F z.1 ∘ c) WI z.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ)) -
    ((hR z i j : ℂ) + Complex.I * (hI z i j : ℂ))

/-- The full original physical tensor is exactly the native row operator of
the same finite reduced residual, throughout the actual joint domain. -/
theorem actual_secondary_physical_error_eq_reduced
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (chart : Ep → OpenPartialHomeomorph M D)
    (hchart : ∀ p, chart p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hOt : ∀ z ∈ O, z.2 ∈ (chart z.1).target)
    (hinj : ∀ z ∈ O, Function.Injective (mfderiv 𝓙 𝓘(ℝ, V) (F z.1) ((chart z.1).symm z.2)))
    (hfree : ∀ z ∈ O,
      let β := incrementsTransversePairing (F z.1) (hF z.1) ((chart z.1).symm z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (chart z.1).symm z.2 a.succ)
      (β.comp β.adjoint).IsInvertible)
    (hR hI : X → Source) (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O)
    (hRsymm : ∀ z ∈ O, ∀ i j, hR z i j = hR z j i)
    (hIsymm : ∀ z ∈ O, ∀ i j, hI z i j = hI z j i)
    (tau : ℝ) (htau : 0 < tau) (length : ℕ) :
    EqOn (actualSecondaryPhysicalError F hF chart hR hI tau length)
      (fun z => actualModeResidualRows
        (actualSecondaryReducedResidual F hF (fun p => (chart p).symm) hR hI tau length z)) O := by
  let c : Ep → D → M := fun p => (chart p).symm
  let source := actualSecondaryComplexSource F hF c hR hI
  let U := actualSecondarySolution F hF c hR hI tau length
  let alpha := (tau : ℂ) / Complex.I
  let v := fun z : X => ((incrementsActualModeStep
    (incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1))
    (incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1)) alpha)^[length]
      (fun x => source (z.1, x))) z.2
  intro z hz
  let Ω := (fun x : D => (z.1, x)) ⁻¹' O
  have hΩ : IsOpen Ω := hO.preimage (continuous_const.prodMk continuous_id)
  have ht : Ω ⊆ (chart z.1).target := fun x hx => hOt (z.1, x) hx
  have hi : ∀ x ∈ Ω, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) (F z.1) ((chart z.1).symm x)) :=
    fun x hx => hinj (z.1, x) hx
  have hf : ∀ x ∈ Ω,
      let β := incrementsTransversePairing (F z.1) (hF z.1) ((chart z.1).symm x)
        (fun a : Fin m => incrementsModeCoordinateDirections (chart z.1).symm x a.succ)
      (β.comp β.adjoint).IsInvertible := fun x hx => hfree (z.1, x) hx
  have hr := actual_joint_contDiffOn_slice hR O hhR z.1
  have hii := actual_joint_contDiffOn_slice hI O hhI z.1
  have hphys := actual_secondary_mode_physical_tensor (F z.1) (hF z.1) (chart z.1) (hchart z.1)
    Ω hΩ ht hi hf (fun x => hR (z.1, x)) (fun x => hI (z.1, x)) hr hii tau htau length z.2 hz
    (hRsymm z hz) (hIsymm z hz)
  obtain ⟨hBR, hJ, _hT, hA, hB⟩ := actual_increment_chosen_chart_coefficients_contDiffOn
    (F z.1) (hF z.1) (chart z.1) (hchart z.1) Ω hΩ ht hi hf
  have hk := incrementsModeComplexSource_zeroFree_contDiffOn (F z.1) (hF z.1) (c z.1)
    (fun x => hR (z.1, x)) (fun x => hI (z.1, x)) Ω hBR hJ hr hii
  have hα : alpha ≠ 0 := div_ne_zero (by exact_mod_cast htau.ne') Complex.I_ne_zero
  have he := incrementsModeActualFiniteResidual_eq (F z.1) (hF z.1) (c z.1)
    alpha hα length (fun x => source (z.1, x)) Ω hΩ hA hB hk z.2 hz
  change actualSecondaryReducedResidual F hF c hR hI tau length z = -v z at he
  funext i j
  change actualSecondaryPhysicalError F hF chart hR hI tau length z i j =
    actualModeResidualRows (actualSecondaryReducedResidual F hF c hR hI tau length z) i j
  rw [actualModeResidualRows_apply, he]
  unfold actualSecondaryPhysicalError
  dsimp only
  dsimp only at hphys
  convert hphys i j using 1
  split_ifs <;> simp only [Pi.neg_apply] <;> dsimp only [v, source, c, alpha, actualSecondaryComplexSource]
  ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_physical_error_eq_reduced
