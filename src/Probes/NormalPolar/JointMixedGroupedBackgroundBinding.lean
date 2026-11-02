import NormalPolar.JointMixedBackgroundBallIdentity
import NormalPolar.PassiveGroupedBackground
import NormalPolar.PassiveGroupedFamilyJoint
import NormalPolar.PassiveRescaledPrimary

/-! Literal bindings for the grouped forcing and the same moving background.
These identities retain the original labels and all within-label cross terms.
The whole original parameter ball lies in the already chosen amplitude ball;
no change of parameter domain is made when applying the two-input supply. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {m N p r : ℕ} {M S P Λ Β : Type*}
  [TopologicalSpace S] [Subsingleton S] [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [Fintype Β]
  {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
variable (s₀ : S) (F : S → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ s, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F s))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
    (m := m) (Λ := Λ) (Β := Β) F)
  (label : (Fin r × Bool) ↪ Fin p)
  (c : (l : Fin r) → Sub l → S → EuclideanSpace ℝ (Fin (m+1)) → M)
  (vf : (l : Fin r) → (a : Sub l) → (s : S) → (x : EuclideanSpace ℝ (Fin (m+1))) →
    normalSpace (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (F s) (c l a s x))
  (phase : Fin r → S × M → ℝ) (tau delta : ℝ) (length probeLength : ℕ)
  (a : (l : Fin r) → Sub l → OpenPartialHomeomorph
    (S × M) (S × EuclideanSpace ℝ (Fin (m+1))))
  (target : (s : S) → (x : M) → LinearMap.BilinForm ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (iteration : ℕ)

theorem jointMixed_passive_rescaled_primary_binding (scale : ℝ) (hs : scale ≠ 0) :
    passiveRescaledPrimary (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) scale hs =
    passiveParameterPrimary s₀ (fun s x => scale • F s x)
      (passiveRescaledPrimary F hF g scale hs) := rfl

theorem jointMixed_grouped_background_moving_binding (u : P → Fin p → ℝ) :
    passiveGroupedFamilyJointBackground (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) label
      (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀)
      (fun l z => phase l (s₀,z.2)) tau delta length probeLength
      (fun l k => passiveParameterChart s₀ (a l k)) (fun _ => target s₀) iteration u =
    jointMixedPassiveBackgroundInput s₀ F hF g length tau delta target
      (jointGroupedParameterPrescribedMean label F hF c vf phase tau probeLength a) iteration u := by
  have hp : (fun (_ : Fin 0 → ℝ) b => jointGroupedParameterPrescribedMean label
      (fun _ : P => F s₀) (fun _ => hF s₀)
      (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀)
      (fun l z => phase l (s₀,z.2)) tau probeLength
      (fun l k => passiveParameterChart s₀ (a l k)) (u b) b) =
      (fun (_ : Fin 0 → ℝ) b =>
        jointGroupedParameterPrescribedMean label F hF c vf phase tau probeLength a (u b) s₀) := by
    funext v b x
    exact passiveGroupedPrescribed_mean s₀ label F hF c vf phase tau probeLength a (u b) b x
  unfold passiveGroupedFamilyJointBackground jointMixedPassiveBackgroundInput
  rw [hp]

theorem jointMixed_grouped_background_fixed_native_binding
    {Ep : Type*} [TopologicalSpace Ep]
    (B : OpenPartialHomeomorph P Ep) (v : Fin p → ℝ) :
    (fun t => actualParameterBackgroundMeanIterate (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) length tau delta (fun _ => target s₀)
      (jointGroupedParameterPrescribedMean label (fun _ : P => F s₀) (fun _ => hF s₀)
        (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀)
        (fun l z => phase l (s₀,z.2)) tau probeLength
        (fun l k => passiveParameterChart s₀ (a l k))) iteration v (B.symm t)) =
    (fun _ : Ep => actualParameterBackgroundMeanIterate F hF g length tau delta target
      (jointGroupedParameterPrescribedMean label F hF c vf phase tau probeLength a) iteration v s₀) := by
  rw [passiveGroupedBackground_prescribed_iterate s₀ F hF g label c vf phase tau delta
    length probeLength a target iteration v]

section Ball
variable [T2Space P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin p)) ∞ P]

theorem jointMixed_original_ball_amplitude_bound
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin p)))
    (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/(‖(EuclideanSpace.equiv (Fin p) ℝ).toContinuousLinearMap‖+1))
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (v : Fin p → ℝ)
    (hv : v ∈ Metric.ball 0 (actualRepairParameterRadius (tensorChartFamilyOfAtlas B))) :
    ‖v‖ ≤ amplitude := by
  have hi := passiveOriginalSmallParameter_original_ball_identity B amplitude ha hbuffer b p₀ hp₀ v
    (by simpa only [Metric.mem_ball,dist_zero_right] using hv)
  have hb := passiveOriginalSmallParameter_bound B amplitude ha b p₀
    (actualRepairParameterMap (tensorChartFamilyOfAtlas B) b p₀ v)
  rwa [hi] at hb
end Ball

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointMixed_grouped_background_moving_binding
#print axioms GlobalEmbedding.Continuation.jointMixed_passive_rescaled_primary_binding
#print axioms GlobalEmbedding.Continuation.jointMixed_grouped_background_fixed_native_binding
#print axioms GlobalEmbedding.Continuation.jointMixed_original_ball_amplitude_bound
