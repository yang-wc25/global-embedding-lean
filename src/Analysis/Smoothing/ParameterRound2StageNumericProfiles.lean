import Smoothing.ParameterRound2OriginalSmoothingStageData
import Smoothing.ParameterRound2IdentityRawCosts

/-! The numeric stage profiles are fixed before all atlases, labels and
actual inputs. Their signs follow from the same genuine stage budgets and
from explicit original raw costs. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem parameterRound2_original_stage_budget_nonneg
    (Data : IncrementsOriginalNativeData n d N M P)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ) (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (r : ℕ) (budget : ℝ) (reference givenPacket : ℕ → ℝ)
    (stage : ParameterRound2OriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference givenPacket) :
    0 ≤ budget ∧ (∀ j, 0 ≤ reference j) ∧ (∀ j, 0 ≤ givenPacket j) :=
  ⟨ENNReal.toReal_nonneg.trans stage.old_pair_budget,
    fun j => ENNReal.toReal_nonneg.trans (stage.reference_bound j),
    fun j => ENNReal.toReal_nonneg.trans (stage.given_bound j)⟩

theorem parameterRound2_stage_numeric_profiles_nonneg
    (m d N q : ℕ) (Cmap Ctarget reference givenPacket : ℕ → ℝ) (budget : ℝ)
    (hCmap : ∀ j, 0 ≤ Cmap j) (hCtarget : ∀ j, 0 ≤ Ctarget j)
    (hbudget : 0 ≤ budget) (hreference : ∀ j, 0 ≤ reference j)
    (rho c cT Bnative : ℝ) (hrho : 0 < rho)
    (Tinv Forward Meta : ℕ → ℝ) (hForward : ∀ k, 0 ≤ Forward k) :
    let B0 := fun j => Ctarget j*budget+(j+1)*reference j
    let Packet := fun j => max (Cmap j*budget) (max (B0 j) (givenPacket j))
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*Packet 0+1))
    let Bnd := fun s R => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT Bnative (Meta (s+(q+4))) R Tinv
    let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4))) c cT Bnative Tinv
    let Dinput := fun s => parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Tinv
    let Tfixed := parameterRound2_identityRawTransition m d Packet Forward
    (∀ j, 0 ≤ B0 j) ∧ (∀ j, 0 ≤ Packet j) ∧ 0 < radius ∧
      (∀ s R, 0 ≤ Bnd s R) ∧ (∀ s, 0 ≤ Mg s) ∧
      (∀ s, 0 ≤ Dinput s) ∧ (∀ k, 0 ≤ Tfixed k) := by
  intro B0 Packet radius Bnd Mg Dinput Tfixed
  have hB0 (j) : 0 ≤ B0 j := add_nonneg (mul_nonneg (hCtarget j) hbudget)
    (mul_nonneg (by positivity) (hreference j))
  have hPacket (j) : 0 ≤ Packet j := (mul_nonneg (hCmap j) hbudget).trans (le_max_left _ _)
  have hr : 0 < radius := by
    have hp0 := hPacket 0
    dsimp only [radius]
    positivity
  exact ⟨hB0,hPacket,hr,
    fun s R => parameterRound2_identityRawBnd_nonneg m d N (s+(q+4)) _ c cT Bnative _ R (hPacket _) Tinv,
    fun s => parameterRound2_identityRawMg_nonneg m d N (s+(q+4)) _ c cT Bnative Tinv,
    fun s => parameterRound2_identityRawDinput_nonneg m d (s+(q+4)) _ (hPacket _) Tinv,
    fun k => parameterRound2_identityRawTransition_nonneg m d Packet Forward hPacket hForward k⟩

#print axioms parameterRound2_original_stage_budget_nonneg
#print axioms parameterRound2_stage_numeric_profiles_nonneg
end GlobalEmbedding.Continuation
