import Probes.Round3ParameterSecondaryPullback
import Probes.Round3ParameterSecondaryLocality

/-!
# Parameter-chart naturality of the complete secondary reconstruction

The physical parameter space is arbitrary.  The two inputs are the real and
imaginary forcing of the actual finite inhomogeneous solver; they need agree
only on the genuine adapted target.  In particular this result also applies
to forcing assembled from the combined background and prescribed primary
family.  It makes no identification of that combined family with the ordinary
background-only family.

No response estimate, displacement identity, or derivative identity is an
input.  The actual reconstruction and its supported wave are compared using
open-target locality of the finite solver.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {P Q M : Type*} [TopologicalSpace P] [TopologicalSpace Q]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M]

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Source" => Fin (m + 1) → Fin (m + 1) → ℝ

variable (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ p, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (F p))
  (c : P → EuclideanSpace ℝ (Fin (m + 1)) → M)
  (a : OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m + 1))))
  (B : OpenPartialHomeomorph P Q)
  (R J : P × EuclideanSpace ℝ (Fin (m + 1)) → Fin (m + 1) → Fin (m + 1) → ℝ)
  (RQ IQ : Q × EuclideanSpace ℝ (Fin (m + 1)) → Fin (m + 1) → Fin (m + 1) → ℝ)
  (hR : ∀ t ∈ B.target, ∀ x, (B.symm t, x) ∈ a.target → RQ (t, x) = R (B.symm t, x))
  (hI : ∀ t ∈ B.target, ∀ x, (B.symm t, x) ∈ a.target → IQ (t, x) = J (B.symm t, x))

include hR hI

theorem actual_secondary_parameter_channels_pullback
    (tau : ℝ) (length : ℕ) (t : Q) (ht : t ∈ B.target)
    (x : D) (hx : (B.symm t, x) ∈ a.target) :
    actualSecondaryRealChannel (fun q => F (B.symm q)) (fun q => hF (B.symm q))
      (fun q => c (B.symm q)) RQ IQ tau length (t, x) =
        actualSecondaryRealChannel F hF c R J tau length (B.symm t, x) ∧
    actualSecondaryImagChannel (fun q => F (B.symm q)) (fun q => hF (B.symm q))
      (fun q => c (B.symm q)) RQ IQ tau length (t, x) =
        actualSecondaryImagChannel F hF c R J tau length (B.symm t, x) := by
  let O : Set D := {y | (B.symm t, y) ∈ a.target}
  have hO : IsOpen O := a.open_target.preimage (continuous_const.prodMk continuous_id)
  let RP : Q × D → Source := fun z => R (B.symm z.1, z.2)
  let IP : Q × D → Source := fun z => J (B.symm z.1, z.2)
  have hr : EqOn (fun y => RQ (t, y)) (fun y => RP (t, y)) O := by
    intro y hy
    exact hR t ht y hy
  have hi : EqOn (fun y => IQ (t, y)) (fun y => IP (t, y)) O := by
    intro y hy
    exact hI t ht y hy
  exact ⟨round3ParameterSecondary_realChannel_eqOn
      (fun q => F (B.symm q)) (fun q => hF (B.symm q)) (fun q => c (B.symm q))
      RQ IQ RP IP t O hr hi hO tau length hx,
    round3ParameterSecondary_imagChannel_eqOn
      (fun q => F (B.symm q)) (fun q => hF (B.symm q)) (fun q => c (B.symm q))
      RQ IQ RP IP t O hr hi hO tau length hx⟩

theorem actual_secondary_parameter_supported_pullback
    (ha : Round3ParameterChartPreserves a) (psi : P × M → ℝ)
    (tau : ℝ) (length : ℕ) (t : Q) (ht : t ∈ B.target) (x : M) :
    round3ParameterSupportedWave
      (fun q => F (B.symm q)) (fun q => hF (B.symm q)) (fun q => c (B.symm q))
      RQ IQ (round3ParameterChartPullback B a) (fun z => psi (B.symm z.1, z.2))
      tau length (t, x) =
    round3ParameterSupportedWave F hF c R J a psi tau length (B.symm t, x) := by
  classical
  have hi := round3ParameterChartPullback_source_iff B a ha (t, x) ht
  by_cases hx : (B.symm t, x) ∈ a.source
  · have hb := hi.mpr hx
    have hqa : round3ParameterChartPullback B a (t, x) =
        (t, (a (B.symm t, x)).2) := by
      rw [round3ParameterChartPullback_apply, ha _ hx]
      simp only [B.right_inv ht]
    have hp : a (B.symm t, x) = (B.symm t, (a (B.symm t, x)).2) :=
      Prod.ext (ha _ hx) rfl
    have htarget : (B.symm t, (a (B.symm t, x)).2) ∈ a.target := by
      rw [← hp]
      exact a.map_source hx
    obtain ⟨hr, hj⟩ := actual_secondary_parameter_channels_pullback
      F hF c a B R J RQ IQ hR hI tau length t ht _ htarget
    simp only [round3ParameterSupportedWave]
    rw [ite_eq_left hb, ite_eq_left hb, ite_eq_left hx, ite_eq_left hx, hqa, hr, hj, hp]
  · have hb := mt hi.mp hx
    simp only [round3ParameterSupportedWave]
    rw [ite_eq_right hb, ite_eq_right hb, ite_eq_right hx, ite_eq_right hx]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_parameter_channels_pullback
#print axioms GlobalEmbedding.Continuation.actual_secondary_parameter_supported_pullback
