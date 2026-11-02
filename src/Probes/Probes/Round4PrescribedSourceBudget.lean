import Probes.ActualPairedProbeSource

/-!
# Actual paired sources: a budget for every real parameter vector

The two genuine source columns are s and -i*s. Their sum has a dimension-free
bound for arbitrary parameter vectors, which can be fed directly to the
original finite reconstruction estimate before taking any mean coefficient.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace ℂ Y]
  [IsScalarTower ℝ ℂ Y] {p r : ℕ}

theorem round4_paired_source_weighted_jets
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r) (s : X → Y)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hs : ContDiffOn ℝ ∞ s O) (n : ℕ) (ell K : ℝ) (hell : 0 ≤ ell)
    (hsb : ∀ a ≤ n, ∀ z ∈ S, ell^a * ‖iteratedFDeriv ℝ a s z‖ ≤ K)
    (u : Fin p → ℝ) :
    ContDiffOn ℝ ∞ (finiteProbeSource (pairedProbeSourceDictionary label l s) u) O ∧
      ∀ a ≤ n, ∀ z ∈ S, ell^a *
        ‖iteratedFDeriv ℝ a (finiteProbeSource (pairedProbeSourceDictionary label l s) u) z‖ ≤
          2*K*‖u‖ := by
  have he : finiteProbeSource (pairedProbeSourceDictionary label l s) u =
      fun z => u (label (l,false)) • s z + u (label (l,true)) • ((-Complex.I) • s z) :=
    funext (finiteProbeSource_paired_dictionary label l s u)
  rw [he]
  refine ⟨(hs.const_smul _).add ((hs.const_smul (-Complex.I)).const_smul _),?_⟩
  intro a ha z hz
  have hsz : ContDiffAt ℝ a s z := (hs.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp)
  have hjet : ‖iteratedFDeriv ℝ a (fun y =>
      u (label (l,false)) • s y + u (label (l,true)) • ((-Complex.I) • s y)) z‖ ≤
      (2*‖u‖)*‖iteratedFDeriv ℝ a s z‖ := by
    rw [fun_iteratedFDeriv_add_apply (hsz.const_smul _) ((hsz.const_smul (-Complex.I)).const_smul _),
      iteratedFDeriv_const_smul_apply' hsz,
      iteratedFDeriv_const_smul_apply' (hsz.const_smul (-Complex.I)),
      iteratedFDeriv_const_smul_apply' hsz]
    calc
      _ ≤ ‖u (label (l,false)) • iteratedFDeriv ℝ a s z‖ +
          ‖u (label (l,true)) • ((-Complex.I) • iteratedFDeriv ℝ a s z)‖ := norm_add_le _ _
      _ = (‖u (label (l,false))‖+‖u (label (l,true))‖)*‖iteratedFDeriv ℝ a s z‖ := by
        simp only [norm_smul,norm_neg,Complex.norm_I,one_mul]
        ring
      _ ≤ (‖u‖+‖u‖)*‖iteratedFDeriv ℝ a s z‖ :=
        mul_le_mul_of_nonneg_right (add_le_add (norm_le_pi_norm u _) (norm_le_pi_norm u _))
          (norm_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ell^a*((2*‖u‖)*‖iteratedFDeriv ℝ a s z‖) :=
      mul_le_mul_of_nonneg_left hjet (pow_nonneg hell a)
    _ = (2*‖u‖)*(ell^a*‖iteratedFDeriv ℝ a s z‖) := by ring
    _ ≤ (2*‖u‖)*K := mul_le_mul_of_nonneg_left (hsb a ha z hz) (by positivity)
    _ = _ := by ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4_paired_source_weighted_jets
