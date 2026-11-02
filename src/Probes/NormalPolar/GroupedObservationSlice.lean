import NormalPolar.JointSecondaryGroupedProfiles
import Probes.ActualSourceRestriction

/-! Restrict genuine joint observation profiles to a fixed parameter slice.
The observer, original sample, and open differentiation domain are the exact
preimages under the norm-one fixed-parameter inclusion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {E H M Ep P Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {m N r : ℕ} {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def JointGroupedPrescribedObservationProfiles.fixedParameter
    {F : Ep → M → V} {hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)}
    {c : (l : Fin r) → Sub l → Ep → D → M}
    {chi : (l : Fin r) → Sub l → X → ℝ}
    {nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x)}
    {a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X}
    {W : Set (Ep × M)} {pieceK : (l : Fin r) → Sub l → Set (Ep × M)}
    {n j : ℕ} {ell Mg Bchi Bnu : ℝ}
    {kappa : P × Y → Ep × M} {Omega S : Set (P × Y)} {T : ℕ → ℝ}
    {phase : Fin r → Ep × M → ℝ} {Mphase : ℝ}
    (profiles : JointGroupedPrescribedObservationProfiles F hF c chi nu a W pieceK
      n j ell Mg Bchi Bnu kappa Omega S T phase Mphase)
    (b : P) (hS : S ⊆ Omega) (hell : 0 ≤ ell) :
    JointGroupedPrescribedObservationProfiles F hF c chi nu a W pieceK
      n j ell Mg Bchi Bnu (fun y => kappa (b,y))
      ((fun y => (b,y)) ⁻¹' Omega) ((fun y => (b,y)) ⁻¹' S) T phase Mphase where
  raw := profiles.raw
  domains := fun l s => (fun y => (b,y)) ⁻¹' profiles.domains l s
  domains_open := fun l s => (profiles.domains_open l s).preimage (continuous_const.prodMk continuous_id)
  active_domain := fun l s _ hy => profiles.active_domain l s hy
  source := fun l s _ hy => profiles.source l s hy
  transition_smooth := fun l s => (profiles.transition_smooth l s).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hy => hy)
  sample := fun l s _ hy => profiles.sample l s _ hy
  transition_jets := by
    intro l s k hk hkj y hy
    have hm : (b,y) ∈ profiles.domains l s :=
      profiles.active_domain l s ⟨hS hy.1,hy.2⟩
    have h := norm_iteratedFDeriv_fixed_parameter_slice_le
      (a l s ∘ kappa) (profiles.domains l s) (profiles.domains_open l s)
      (profiles.transition_smooth l s) b y hm k
    exact (mul_le_mul_of_nonneg_left h (pow_nonneg hell (k-1))).trans
      (profiles.transition_jets l s k hk hkj (b,y) hy)
  phase_smooth := fun l s => (profiles.phase_smooth l s).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hy => hy)
  phase_jets := by
    intro l s k hkj y hy
    have hm : (b,y) ∈ profiles.domains l s :=
      profiles.active_domain l s ⟨hS hy.1,hy.2⟩
    have h := norm_iteratedFDeriv_fixed_parameter_slice_le
      (phase l ∘ kappa) (profiles.domains l s) (profiles.domains_open l s)
      (profiles.phase_smooth l s) b y hm (k+1)
    exact (mul_le_mul_of_nonneg_left h (pow_nonneg hell k)).trans
      (profiles.phase_jets l s k hkj (b,y) hy)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.JointGroupedPrescribedObservationProfiles.fixedParameter
