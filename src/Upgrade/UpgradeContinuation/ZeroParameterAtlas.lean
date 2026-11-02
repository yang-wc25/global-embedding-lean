import NormalPolar.PassiveOriginalParameterRaw
import Smoothing.Round4ParameterEtaTransfer

/-!
# The literal zero-dimensional reference parameter atlas

The passive probe construction requires its reference increment data to use
an identity parameter chart.  The compact manifold of passive probe
parameters is introduced later; the reference seed itself has no parameter.
Here its one chart is literally `refl`, with the actual constant raw cutoff.
All sampling domains are the unchanged zero-dimensional vector space.
-/

noncomputable section
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical

namespace GlobalEmbedding.Continuation.UpgradeContinuation

abbrev ZeroParameter := EuclideanSpace ℝ (Fin 0)

/-- The reference parameter chart is the identity, including off its source. -/
def zeroParameterAtlas : BufferedAtlas ZeroParameter ZeroParameter where
  count := 1
  chart := fun _ => OpenPartialHomeomorph.refl ZeroParameter
  inner := fun _ => univ
  inner_open := fun _ => isOpen_univ
  inner_subset := fun _ => Subset.rfl
  cover := fun _ => ⟨0, mem_univ _⟩
  buffer := 1
  buffer_pos := zero_lt_one
  buffered := fun _ _ _ => subset_univ _
  support := fun _ => univ

theorem zeroParameterAtlas_smooth : IsSmoothBufferedAtlas zeroParameterAtlas := by
  constructor
  · intro i
    change OpenPartialHomeomorph.refl ZeroParameter ∈ maximalAtlas 𝓘(ℝ,ZeroParameter) ∞ ZeroParameter
    simpa only [chartAt_self_eq] using
      (chart_mem_maximalAtlas (I := 𝓘(ℝ,ZeroParameter)) (n := ∞) (0 : ZeroParameter))
  · exact fun _ => Subset.rfl

theorem zeroParameterAtlas_forward (i : Fin zeroParameterAtlas.count) :
    ContMDiff 𝓘(ℝ,ZeroParameter) 𝓘(ℝ,ZeroParameter) ∞ (zeroParameterAtlas.chart i) :=
  contMDiff_id

/-- A genuine raw preparation: the unique chart carries the constant one
cutoff.  The bounds are numerical and the support degree is the actual graph. -/
def zeroParameterRaw :
    TensorRawCutoffPreparation zeroParameterAtlas (fun _ => 1) (fun _ => 1)
      zeroParameterAtlas.supportDegree where
  raw := fun _ _ => 1
  smooth := fun _ => contMDiff_const
  plateau_cover := fun _ => ⟨⟨0,by decide⟩,rfl⟩
  inner_support := fun _ => subset_univ _
  enlarged_support := fun _ => subset_univ _
  degree := le_rfl
  own_jets := by
    intro i k y hy
    change ‖iteratedFDeriv ℝ k (fun _ : ZeroParameter => (1 : ℝ)) y‖ ≤ 1
    cases k with
    | zero => simp only [norm_iteratedFDeriv_zero, norm_one, le_refl]
    | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, zero_le_one]
  transition_jets := by
    intro p i k hk y hy hactive
    exact round4_positive_identity_jet_norm_le k hk y

theorem zeroParameterAtlas_norm (p : ZeroParameter) : ‖p‖ = 0 := by
  have hp : p = 0 := Subsingleton.elim _ _
  simp only [hp, norm_zero]

theorem zeroParameterAtlas_compact : IsCompact (univ : Set ZeroParameter) := by
  have h : (univ : Set ZeroParameter) = {0} := by
    ext p
    simp only [mem_univ, mem_singleton_iff, true_iff]
    exact Subsingleton.elim _ _
  rw [h]
  exact isCompact_singleton

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.zeroParameterRaw
#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.zeroParameterAtlas_smooth
