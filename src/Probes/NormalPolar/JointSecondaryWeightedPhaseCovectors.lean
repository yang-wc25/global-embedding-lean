import NormalPolar.JointSecondaryNativePerturbation
import Probes.ActualSecondaryConstructedSum
import GlobalEmbedding.Paper.GoodCovectorRescaling

/-! Literal differential identities for weighted and signed original phase
functions. The displayed covectors use the canonical scalar tangent cast;
all identities are proved only where the original functions are smooth. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {M Label : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

theorem jointSecondaryPhaseCovector_const_mul (psi : M → ℝ) (x : M)
    (hpsi : MDifferentiableAt IM 𝓘(ℝ,ℝ) psi x) (c : ℝ) :
    jointSecondaryPhaseCovector (m := m) (fun y => c * psi y) x = c • jointSecondaryPhaseCovector (m := m) psi x := by
  exact (hpsi.hasMFDerivAt.const_smul c).mfderiv

theorem jointSecondaryPhaseCovector_add (psi phi : M → ℝ) (x : M)
    (hpsi : MDifferentiableAt IM 𝓘(ℝ,ℝ) psi x)
    (hphi : MDifferentiableAt IM 𝓘(ℝ,ℝ) phi x) :
    jointSecondaryPhaseCovector (m := m) (fun y => psi y + phi y) x =
      jointSecondaryPhaseCovector (m := m) psi x + jointSecondaryPhaseCovector (m := m) phi x := by
  exact (hpsi.hasMFDerivAt.add hphi.hasMFDerivAt).mfderiv

theorem jointSecondaryPhaseCovector_sub (psi phi : M → ℝ) (x : M)
    (hpsi : MDifferentiableAt IM 𝓘(ℝ,ℝ) psi x)
    (hphi : MDifferentiableAt IM 𝓘(ℝ,ℝ) phi x) :
    jointSecondaryPhaseCovector (m := m) (fun y => psi y - phi y) x =
      jointSecondaryPhaseCovector (m := m) psi x - jointSecondaryPhaseCovector (m := m) phi x := by
  exact (hpsi.hasMFDerivAt.sub hphi.hasMFDerivAt).mfderiv

theorem jointSecondaryPhaseCovector_neg (psi : M → ℝ) (x : M) :
    jointSecondaryPhaseCovector (m := m) (fun y => -psi y) x = -jointSecondaryPhaseCovector (m := m) psi x := by
  exact mfderiv_neg

def jointSecondarySpatialSignedPhase (phase : Label → M → ℝ)
    (rec : (Label × Label) × Fin 4) : M → ℝ :=
  fun x => ![phase rec.1.1 x+phase rec.1.2 x,phase rec.1.1 x-phase rec.1.2 x,
    -phase rec.1.1 x+phase rec.1.2 x,-phase rec.1.1 x-phase rec.1.2 x] rec.2

theorem jointSecondarySpatialSignedPhase_smooth
    (phase : Label → M → ℝ) (O : Label → Set M)
    (hphase : ∀ l, ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ (phase l) (O l))
    (rec : (Label × Label) × Fin 4) :
    ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ (jointSecondarySpatialSignedPhase phase rec)
      (O rec.1.1 ∩ O rec.1.2) := by
  have h₁ := (hphase rec.1.1).mono (inter_subset_left : O rec.1.1 ∩ O rec.1.2 ⊆ _)
  have h₂ := (hphase rec.1.2).mono (inter_subset_right : O rec.1.1 ∩ O rec.1.2 ⊆ _)
  rcases rec with ⟨⟨l,l'⟩,q⟩
  fin_cases q
  · exact h₁.add h₂
  · exact h₁.sub h₂
  · exact h₁.neg.add h₂
  · exact h₁.neg.sub h₂

theorem jointSecondarySpatialSignedPhase_good
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (phase : Label → M → ℝ) (rec : ActualSecondarySignedRecord Label) (x : M)
    (h₁ : MDifferentiableAt IM 𝓘(ℝ,ℝ) (phase rec.val.1.1) x)
    (h₂ : MDifferentiableAt IM 𝓘(ℝ,ℝ) (phase rec.val.1.2) x)
    (hplus : GoodCovector F hF x (jointSecondaryPhaseCovector (m := m) (phase rec.val.1.1) x +
      jointSecondaryPhaseCovector (m := m) (phase rec.val.1.2) x))
    (hminus : rec.val.1.1 ≠ rec.val.1.2 → GoodCovector F hF x
      (jointSecondaryPhaseCovector (m := m) (phase rec.val.1.1) x -
        jointSecondaryPhaseCovector (m := m) (phase rec.val.1.2) x)) :
    GoodCovector F hF x (mfderiv IM 𝓘(ℝ,ℝ) (jointSecondarySpatialSignedPhase phase rec.val) x) := by
  rw [← jointSecondaryPhaseCovector_eq]
  rcases rec with ⟨⟨⟨l,l'⟩,q⟩,hr⟩
  have hneg (xi : TangentSpace IM x →L[ℝ] ℝ) (hg : GoodCovector F hF x xi) :
      GoodCovector F hF x (-xi) := by
    have heq : (-1:ℝ) • xi = -xi := by
      ext v
      simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.neg_apply,
        smul_eq_mul,neg_one_mul]
    have hh := (good_covector_smul_iff F hF x xi (-1:ℝ) (by norm_num)).mpr hg
    rwa [heq] at hh
  fin_cases q
  · change GoodCovector F hF x (jointSecondaryPhaseCovector (m := m) (fun y => phase l y+phase l' y) x)
    rw [jointSecondaryPhaseCovector_add _ _ x h₁ h₂]
    exact hplus
  · have hne : l ≠ l' := by simpa using hr
    change GoodCovector F hF x (jointSecondaryPhaseCovector (m := m) (fun y => phase l y-phase l' y) x)
    rw [jointSecondaryPhaseCovector_sub _ _ x h₁ h₂]
    exact hminus hne
  · have hne : l ≠ l' := by simpa using hr
    have hf : (fun y => -phase l y+phase l' y) = (fun y => -(phase l y-phase l' y)) := by
      funext y
      ring
    change GoodCovector F hF x (jointSecondaryPhaseCovector (m := m) (fun y => -phase l y+phase l' y) x)
    rw [hf,jointSecondaryPhaseCovector_neg,jointSecondaryPhaseCovector_sub _ _ x h₁ h₂]
    exact hneg _ (hminus hne)
  · have hf : (fun y => -phase l y-phase l' y) = (fun y => -(phase l y+phase l' y)) := by
      funext y
      ring
    change GoodCovector F hF x (jointSecondaryPhaseCovector (m := m) (fun y => -phase l y-phase l' y) x)
    rw [hf,jointSecondaryPhaseCovector_neg,jointSecondaryPhaseCovector_add _ _ x h₁ h₂]
    exact hneg _ hplus

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondarySpatialSignedPhase_good
