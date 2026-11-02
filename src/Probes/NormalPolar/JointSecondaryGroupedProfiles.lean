import NormalPolar.JointSecondaryGroupedAmplitude
import NormalPolar.ParameterDisplacementPrescribedWave

/-! Actual raw observation data for finitely many pieces of each original
prescribed label. The finite piece type may vary with the label. Every field
concerns the original geometry, original cutoff or actual transition; there
are no estimates for reconstructed coefficients, means or secondary outputs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {m N r : ℕ} {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

structure JointGroupedPrescribedObservationProfiles
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M)
    (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (pieceK : (l : Fin r) → Sub l → Set (Ep × M))
    (n j : ℕ) (ell Mg Bchi Bnu : ℝ)
    (kappa : Y → Ep × M) (Omega S : Set Y) (T : ℕ → ℝ)
    (phase : Fin r → Ep × M → ℝ) (Mphase : ℝ) where
  raw : ∀ l s, ActualPrescribedSpatialRawProfiles F hF (c l s) (chi l s) (nu l s)
    (a l s) W (pieceK l s) n j ell Mg Bchi Bnu
  domains : (l : Fin r) → Sub l → Set Y
  domains_open : ∀ l s, IsOpen (domains l s)
  active_domain : ∀ l s, Omega ∩ kappa ⁻¹' pieceK l s ⊆ domains l s
  source : ∀ l s, MapsTo kappa (domains l s) (a l s).source
  transition_smooth : ∀ l s, ContDiffOn ℝ ∞ (a l s ∘ kappa) (domains l s)
  sample : ∀ l s y, y ∈ S ∩ kappa ⁻¹' pieceK l s → a l s (kappa y) ∈ (raw l s).sample
  transition_jets : ∀ l s k, 1 ≤ k → k ≤ j → ∀ y ∈ S ∩ kappa ⁻¹' pieceK l s,
    ell^(k-1)*‖iteratedFDeriv ℝ k (a l s ∘ kappa) y‖ ≤ T k
  phase_smooth : ∀ l s, ContDiffOn ℝ ∞ (phase l ∘ kappa) (domains l s)
  phase_jets : ∀ l s k, k < j → ∀ y ∈ S ∩ kappa ⁻¹' pieceK l s,
    ell^k*‖iteratedFDeriv ℝ (k+1) (phase l ∘ kappa) y‖ ≤ Mphase

/-- Reuse the single-piece raw producer at its original label. Repeating its
primitive input across the unused labels introduces no new wave or label;
the selected output is precisely the original (l,s) reconstruction. -/
def JointGroupedPrescribedObservationProfiles.single
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M)
    (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (pieceK : (l : Fin r) → Sub l → Set (Ep × M))
    (n j : ℕ) (ell Mg Bchi Bnu : ℝ)
    (kappa : Y → Ep × M) (Omega S : Set Y) (T : ℕ → ℝ)
    (phase : Fin r → Ep × M → ℝ) (Mphase : ℝ)
    (profiles : JointGroupedPrescribedObservationProfiles F hF c chi nu a W pieceK n j
      ell Mg Bchi Bnu kappa Omega S T phase Mphase) (l : Fin r) (s : Sub l) :
    ActualPrescribedObservationProfiles F hF (fun _ : Fin r => c l s)
      (fun _ : Fin r => chi l s) (fun _ : Fin r => nu l s) (fun _ : Fin r => a l s)
      W (fun _ : Fin r => pieceK l s) n j ell Mg Bchi Bnu kappa Omega S T
      (fun _ : Fin r => phase l) Mphase where
  raw := fun _ => profiles.raw l s
  domains := fun _ => profiles.domains l s
  domains_open := fun _ => profiles.domains_open l s
  active_domain := fun _ => profiles.active_domain l s
  source := fun _ => profiles.source l s
  transition_smooth := fun _ => profiles.transition_smooth l s
  sample := fun _ => profiles.sample l s
  transition_jets := fun _ => profiles.transition_jets l s
  phase_smooth := fun _ => profiles.phase_smooth l s
  phase_jets := fun _ => profiles.phase_jets l s

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.JointGroupedPrescribedObservationProfiles.single
