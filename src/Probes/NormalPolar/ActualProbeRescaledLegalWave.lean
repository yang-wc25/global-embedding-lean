import Upgrade.ProbeInterface
import GlobalEmbedding.Offline.ImmersionRescaling

/-!
# The original legal wave on the actual contracted reference map

A nonzero scalar contraction changes the true second form by that scalar
and preserves the actual normal submodule.  The original normal vector is
therefore transported by its unchanged ambient value.  The actual legal
wave keeps its phase, cutoff, leading value and rank-one tensor exactly.
This supplies the primitive amplitude binding for G0 = sqrt(1-t^20) F0.
-/

noncomputable section
open Set Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

def actualRescaledNormal (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (c : ℝ) (hc : c ≠ 0) (x : M) (nu : normalSpace (I := IM) F x) :
    normalSpace (I := IM) (c • F) x :=
  ⟨nu, by rw [normalSpace_const_rescale F hF c hc]; exact nu.property⟩

theorem actualRescaledNormal_value (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (c : ℝ) (hc : c ≠ 0) (x : M) (nu : normalSpace (I := IM) F x) :
    (actualRescaledNormal F hF c hc x nu : V) = (nu : V) := rfl

theorem actualRescaledNormal_legal (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (c : ℝ) (hc : c ≠ 0) (x : M) (xi : TangentSpace IM x →ₗ[ℝ] ℝ)
    (nu : normalSpace (I := IM) F x)
    (hnu : nu ∈ supportedRankLegalValueSpace (trueSecondForm F hF x) xi) :
    actualRescaledNormal F hF c hc x nu ∈
      supportedRankLegalValueSpace (trueSecondForm (c • F) (contMDiff_const_rescale F hF c) x) xi := by
  apply (supportedRank_mem_legalValueSpace_iff _ _ _).mpr
  intro q
  have hOld := (supportedRank_mem_legalValueSpace_iff _ _ _).mp hnu q
  have hForm := DFunLike.congr_fun (trueSecondForm_const_rescale F hF c hc x)
    (symmetricSquareLinearMap xi.ker.subtype q)
  change (trueSecondForm (c • F) (contMDiff_const_rescale F hF c) x
    (symmetricSquareLinearMap xi.ker.subtype q) : V) =
      c • (trueSecondForm F hF x (symmetricSquareLinearMap xi.ker.subtype q) : V) at hForm
  change inner ℝ (trueSecondForm (c • F) (contMDiff_const_rescale F hF c) x
    (symmetricSquareLinearMap xi.ker.subtype q) : V) (nu : V) = 0
  rw [hForm, real_inner_smul_left]
  exact mul_eq_zero_of_right c hOld

def actualRescaledLegalWave (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (c : ℝ) (hc : c ≠ 0) (w : LocalLegalWave F hF) :
    LocalLegalWave (c • F) (contMDiff_const_rescale F hF c) where
  center := w.center
  domain := w.domain
  phase := w.phase
  normal := fun x => actualRescaledNormal F hF c hc x (w.normal x)
  cutoff := w.cutoff
  domain_open := w.domain_open
  center_mem := w.center_mem
  domain_chart := w.domain_chart
  support_subset := w.support_subset
  phase_smooth := w.phase_smooth
  normal_smooth := w.normal_smooth
  legal := fun x hx => ⟨(goodCovector_const_rescale_iff F hF c hc x _).mpr (w.legal x hx).1,
    actualRescaledNormal_legal F hF c hc x _ (w.normal x) (w.legal x hx).2⟩

theorem actualRescaledLegalWave_value (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (c : ℝ) (hc : c ≠ 0) (w : LocalLegalWave F hF) :
    (actualRescaledLegalWave F hF c hc w).value = w.value := rfl

theorem actualRescaledLegalWave_tensor (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (c : ℝ) (hc : c ≠ 0) (w : LocalLegalWave F hF) :
    (actualRescaledLegalWave F hF c hc w).tensor = w.tensor := rfl

/-- The original cutoff and unchanged ambient normal section give exactly
the original leading value, on any chosen genuine spatial coordinate map. -/
theorem actualRescaledLegalWave_amplitude_binding
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (c : ℝ) (hc : c ≠ 0) (w : LocalLegalWave F hF)
    {Y : Type*} (kappa : Y → M) (y : Y) :
    w.cutoff (kappa y) •
      (actualRescaledNormal F hF c hc (kappa y) (w.normal (kappa y)) : V) = w.value (kappa y) := rfl

theorem actual_probe_contraction_pos (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    0 < Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) := by
  apply Real.sqrt_pos.mpr
  have hpow : t ^ (20 : ℕ) < 1 := pow_lt_one₀ ht.le ht1 (by decide)
  nlinarith [show (t ^ (10 : ℕ)) ^ 2 = t ^ (20 : ℕ) by ring]

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualRescaledNormal_legal
#print axioms GlobalEmbedding.NormalPolar.actualRescaledLegalWave
#print axioms GlobalEmbedding.NormalPolar.actualRescaledLegalWave_amplitude_binding
#print axioms GlobalEmbedding.NormalPolar.actual_probe_contraction_pos
