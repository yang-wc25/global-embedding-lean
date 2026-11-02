import Probes.Round4PrescribedGlobalSmooth
import Smoothing.ParameterRound2GlobalCorrectionSupport

/-!
# Inactive complete prescribed modes have actual joint zero germs

Relative support of the primitive normal source controls the full finite
reconstruction and its original global extension. After a genuine observation,
all spatial derivative coefficients and the complete opposite contribution have
zero germs. No coefficient-support assumption or outside phase regularity occurs.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {Eq : Type*} [NormedAddCommGroup Eq] [NormedSpace ℝ Eq] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Y" => Eq × D

/-- Actual spatial differentiation preserves a joint amplitude zero germ. -/
theorem round4_complete_observed_coefficient_zero_germ
    {J : Type*} (R Q : Y → V) (phase : Y → ℝ) (tau : ℝ) (directions : J → D) (z : Y)
    (hR : R =ᶠ[𝓝 z] 0) (hQ : Q =ᶠ[𝓝 z] 0) :
    (fun w : Y => fun s : J => incrementsPrimaryDerivativeCoefficient
      (fun x => phase (w.1,x)) tau (fun (_ : Unit) _ => 1)
      (fun _ x => R (w.1,x)) (fun _ x => Q (w.1,x)) w.2 (directions s)) =ᶠ[𝓝 z] 0 := by
  filter_upwards [eventually_eventuallyEq_nhds.mpr hR,eventually_eventuallyEq_nhds.mpr hQ] with w hwR hwQ
  have hs : Tendsto (fun y : D => (w.1,y)) (𝓝 w.2) (𝓝 w) :=
    (continuous_const.prodMk continuous_id).continuousAt.tendsto
  have hr : (fun y : D => R (w.1,y)) =ᶠ[𝓝 w.2] 0 := hwR.comp_tendsto hs
  have hq : (fun y : D => Q (w.1,y)) =ᶠ[𝓝 w.2] 0 := hwQ.comp_tendsto hs
  funext s co
  simp only [incrementsPrimaryDerivativeCoefficient]
  rw [hr.fderiv_eq (𝕜:=ℝ),hq.fderiv_eq (𝕜:=ℝ),hr.eq_of_nhds,hq.eq_of_nhds]
  simp

/-- A full opposite mean has the same actual inactive joint germ. -/
theorem round4_complete_observed_mode_mean_zero_germ
    {J : Type*} (R Q : Y → V) (phase : Y → ℝ) (tau : ℝ) (directions : J → D) (z : Y)
    (hR : R =ᶠ[𝓝 z] 0) (hQ : Q =ᶠ[𝓝 z] 0) (i j : J) :
    (fun w : Y => incrementsOppositePrimaryContribution
      (fun (_ : Unit) s => incrementsPrimaryDerivativeCoefficient
        (fun x => phase (w.1,x)) tau (fun (_ : Unit) _ => 1)
        (fun _ x => R (w.1,x)) (fun _ x => Q (w.1,x)) w.2 (directions s)) i j) =ᶠ[𝓝 z] 0 := by
  filter_upwards [round4_complete_observed_coefficient_zero_germ R Q phase tau directions z hR hQ] with w hw
  have hh : (fun (_ : Unit) s => incrementsPrimaryDerivativeCoefficient
      (fun x => phase (w.1,x)) tau (fun (_ : Unit) _ => 1)
      (fun _ x => R (w.1,x)) (fun _ x => Q (w.1,x)) w.2 (directions s)) = 0 := by
    funext t s co
    exact congrFun (congrFun hw s) co
  rw [hh]
  simp [incrementsOppositePrimaryContribution,dotProduct]

section GlobalSource
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {p r : ℕ}
local notation "X" => Ep × D
local notation "Pspace" => Fin p → ℝ

/-- The primitive source support produces the same actual observed mean germ. -/
theorem round4_prescribed_global_mode_mean_inactive_germ
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (vf : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (tau : ℝ) (length : ℕ) (a : OpenPartialHomeomorph (Ep × M) X)
    (W K : Set (Ep × M)) (hW : IsOpen W)
    (hK : IsClosed (Subtype.val ⁻¹' K : Set W)) (hKsource : K ⊆ a.source)
    (hchart : ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ a a.source)
    (hA : ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (hB : ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (hG : ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) a.target)
    (hJ : ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) a.target)
    (hT : ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c z.1) z.2) a.target)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 k : V)) a.target)
    (hvf : ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) a.target)
    (hinput : ∀ z ∈ a.target, z ∈ tsupport (fun w : X => (vf w.1 w.2 : V)) → a.symm z ∈ K)
    (u : Pspace) (kappa : Y → Ep × M) (z : Y) (hkappa : ContinuousAt kappa z)
    (hzW : kappa z ∈ W) (hzK : kappa z ∉ K) (phase : Ep × M → ℝ)
    {J : Type*} (directions : J → D) (i j : J) :
    let R := fun w => round4PrescribedGlobalAmplitude false label l F hF c vf tau length a u (kappa w)
    let Q := fun w => round4PrescribedGlobalAmplitude true label l F hF c vf tau length a u (kappa w)
    (fun w : Y => incrementsOppositePrimaryContribution
      (fun (_ : Unit) s => incrementsPrimaryDerivativeCoefficient
        (fun x => phase (kappa (w.1,x))) tau (fun (_ : Unit) _ => 1)
        (fun _ x => R (w.1,x)) (fun _ x => Q (w.1,x)) w.2 (directions s)) i j) =ᶠ[𝓝 z] 0 := by
  intro R Q
  have ha (ch : Bool) := round4_prescribed_global_amplitude_smooth ch label l F hF c vf
    tau length a W K hW hK hKsource hchart hA hB hG hJ hT hBR hvf hinput u
  have hr : R =ᶠ[𝓝 z] 0 := parameterRound2_relative_observation_zero_germ
    (round4PrescribedGlobalAmplitude false label l F hF c vf tau length a u)
    W K hW (ha false).2 kappa z hkappa hzW hzK
  have hq : Q =ᶠ[𝓝 z] 0 := parameterRound2_relative_observation_zero_germ
    (round4PrescribedGlobalAmplitude true label l F hF c vf tau length a u)
    W K hW (ha true).2 kappa z hkappa hzW hzK
  exact round4_complete_observed_mode_mean_zero_germ R Q (phase ∘ kappa) tau directions z hr hq i j

end GlobalSource

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_complete_observed_coefficient_zero_germ
#print axioms GlobalEmbedding.Continuation.round4_complete_observed_mode_mean_zero_germ

#print axioms GlobalEmbedding.Continuation.round4_prescribed_global_mode_mean_inactive_germ
