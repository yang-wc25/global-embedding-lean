import Probes.Round4PrescribedGlobalWave

/-!
# Each actual global parameter column belongs to its original prescribed mode

The zero of every other label is derived from the primitive sparse source and
the original finite solver's locality, including its real reconstruction.
Consequently an active chart pullback is exactly the original complete local
mode, not merely its leading trigonometric term.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Pspace" => Fin p → ℝ

theorem round4PrescribedAmplitude_eq_zero_of_pair_zero
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x))
    (tau : ℝ) (length : ℕ) (u : Pspace)
    (hc : u (label (l,false)) = 0) (hs : u (label (l,true)) = 0) (x : D) :
    round4PrescribedAmplitude imag label l F hF c vf tau length u x = 0 := by
  have hsource : actualPairedNormalSource label l F hF c vf u = 0 := by
    rw [actualPairedNormalSource_eq_finite_source]
    funext y
    rw [finiteProbeSource_paired_dictionary]
    simp [hc,hs]
  have hr : incrementsPrimaryReconstructedChannel F hF c
      (if imag then incrementsModeImagPart else incrementsModeRealPart) tau length
      (actualPairedNormalSource label l F hF c vf u) x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    have hh := actual_full_mean_channel_support F hF c
      (if imag then incrementsModeImagPart else incrementsModeRealPart) tau length
      (actualPairedNormalSource label l F hF c vf u) hx
    simpa [hsource] using hh
  simp only [round4PrescribedAmplitude,hr,hc,hs,neg_zero,ite_self,zero_smul,add_zero]

theorem round4PrescribedGlobalAmplitude_eq_zero_of_pair_zero
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (vf : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (tau : ℝ) (length : ℕ) (a : OpenPartialHomeomorph (Ep × M) X)
    (u : Pspace) (hc : u (label (l,false)) = 0) (hs : u (label (l,true)) = 0) (z : Ep × M) :
    round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a u z = 0 := by
  classical
  unfold round4PrescribedGlobalAmplitude
  split_ifs
  · exact round4PrescribedAmplitude_eq_zero_of_pair_zero imag label l (F (a z).1) (hF (a z).1)
      (c (a z).1) (vf (a z).1) tau length u hc hs (a z).2
  · rfl

theorem round4PrescribedGlobalWave_single_mode
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (i : Fin r) (ch : Bool) (z : Ep × M) :
    round4PrescribedGlobalWave label F hF c vf phase tau length a (Pi.single (label (i,ch)) 1) z =
      Real.cos (phase i z/tau) • round4PrescribedGlobalAmplitude false label i F hF (c i) (vf i)
        tau length (a i) (Pi.single (label (i,ch)) 1) z-
      Real.sin (phase i z/tau) • round4PrescribedGlobalAmplitude true label i F hF (c i) (vf i)
        tau length (a i) (Pi.single (label (i,ch)) 1) z := by
  classical
  unfold round4PrescribedGlobalWave
  apply Finset.sum_eq_single i
  · intro k hk hki
    have h0 (imag : Bool) : round4PrescribedGlobalAmplitude imag label k F hF (c k) (vf k)
        tau length (a k) (Pi.single (label (i,ch)) 1) z = 0 := by
      apply round4PrescribedGlobalAmplitude_eq_zero_of_pair_zero
      · simp [Pi.single_apply,label.injective.eq_iff,Ne.symm hki]
      · simp [Pi.single_apply,label.injective.eq_iff,Ne.symm hki]
    rw [h0 false,h0 true]
    simp
  · simp

/-- On its actual chart the global response column is the complete original
local finite mode, including the homogeneous reconstruction and both channels. -/
theorem round4PrescribedGlobalWave_chart_column
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (i : Fin r) (ch : Bool)
    (z : X) (hz : z ∈ (a i).target) :
    round4PrescribedGlobalWave label F hF c vf phase tau length a (Pi.single (label (i,ch)) 1) ((a i).symm z) =
      round4ActualProbeMode label i (F z.1) (hF z.1) (c i z.1) (vf i z.1)
        (fun y => phase i ((a i).symm (z.1,y))) tau length (Pi.single (label (i,ch)) 1) z.2 := by
  classical
  rw [round4PrescribedGlobalWave_single_mode]
  have hamp (imag : Bool) : round4PrescribedGlobalAmplitude imag label i F hF (c i) (vf i)
      tau length (a i) (Pi.single (label (i,ch)) 1) ((a i).symm z) =
      round4PrescribedAmplitude imag label i (F z.1) (hF z.1) (c i z.1) (vf i z.1)
        tau length (Pi.single (label (i,ch)) 1) z.2 := by
    unfold round4PrescribedGlobalAmplitude
    rw [if_pos ((a i).map_target hz)]
    exact congrArg (fun w : X => round4PrescribedAmplitude imag label i (F w.1) (hF w.1)
      (c i w.1) (vf i w.1) tau length (Pi.single (label (i,ch)) 1) w.2) ((a i).right_inv hz)
  rw [hamp false,hamp true]
  exact (round4ActualProbeMode_eq_amplitudes label i (F z.1) (hF z.1) (c i z.1) (vf i z.1)
    (fun y => phase i ((a i).symm (z.1,y))) tau length (Pi.single (label (i,ch)) 1) z.2).symm

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4PrescribedAmplitude_eq_zero_of_pair_zero
#print axioms GlobalEmbedding.Continuation.round4PrescribedGlobalWave_single_mode
#print axioms GlobalEmbedding.Continuation.round4PrescribedGlobalWave_chart_column
