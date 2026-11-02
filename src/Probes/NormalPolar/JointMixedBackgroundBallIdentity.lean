import NormalPolar.PassiveParameterBackground
import NormalPolar.ActualProbeBackgroundDiagonal
import NormalPolar.OriginalWaveSeedParameterBall

/-! The true passive background wave, separately from the other first-map
terms, is the same external-parameter wave on the entire original ball.
This is an identity of the finite solver, before any differentiation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {m N p : ℕ} {M S P Λ Β : Type*}
  [TopologicalSpace S] [Subsingleton S] [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
variable (s₀ : S) (F : S → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ s, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F s))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
    (m := m) (Λ := Λ) (Β := Β) F)
  (length : ℕ) (tau delta : ℝ)
  (target : (s : S) → (x : M) → LinearMap.BilinForm ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (probe : (Fin p → ℝ) → (s : S) → (x : M) → LinearMap.BilinForm ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (iteration : ℕ)

def jointMixedPassiveBackgroundInput (u : P → Fin p → ℝ) :
    (b : P) → (x : M) → LinearMap.BilinForm ℝ
      (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x) :=
  actualParameterBackgroundMeanIterate (fun _ : P => F s₀) (fun _ => hF s₀)
    (passiveParameterPrimary s₀ F g) length tau delta (fun _ => target s₀)
    (fun (_ : Fin 0 → ℝ) b => probe (u b) s₀) iteration 0

def jointMixedSeedBackgroundWave (v : Fin p → ℝ) (x : M) : EuclideanSpace ℝ (Fin N) :=
  round3ParameterPrimaryWave F hF g
    (actualParameterBackgroundMeanIterate F hF g length tau delta target probe iteration v)
    length tau (s₀,x)

theorem jointMixed_passive_background_wave_identity
    (u : P → Fin p → ℝ) (b : P) (x : M) :
    round3ParameterPrimaryWave (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g)
      (jointMixedPassiveBackgroundInput s₀ F hF g length tau delta target probe iteration u)
      length tau (b,x) =
    jointMixedSeedBackgroundWave s₀ F hF g length tau delta target probe iteration (u b) x := by
  unfold jointMixedPassiveBackgroundInput jointMixedSeedBackgroundWave
  rw [actual_parameter_background_diagonal_wave (fun _ : P => F s₀) (fun _ => hF s₀)
    (passiveParameterPrimary s₀ F g) length tau delta (fun _ => target s₀)
    (fun v (_ : P) => probe v s₀) u
    (passiveParameterPrimary_chart_preserves s₀ F g) iteration]
  dsimp only
  rw [passiveParameterBackground_iterate s₀ F hF g length tau delta target probe iteration (u b)]
  exact passiveParameterPrimary_wave s₀ F hF g _ length tau b x

variable [T2Space P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin p)) ∞ P]

theorem jointMixed_passive_background_original_ball
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin p)))
    (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/(‖(EuclideanSpace.equiv (Fin p) ℝ).toContinuousLinearMap‖+1))
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (v : Fin p → ℝ) (hv : ‖v‖ < actualRepairParameterRadius (tensorChartFamilyOfAtlas B)) (x : M) :
    round3ParameterPrimaryWave (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g)
      (jointMixedPassiveBackgroundInput s₀ F hF g length tau delta target probe iteration
        (passiveOriginalSmallParameter B amplitude ha b p₀)) length tau
      (actualRepairParameterMap (tensorChartFamilyOfAtlas B) b p₀ v,x) =
    jointMixedSeedBackgroundWave s₀ F hF g length tau delta target probe iteration v x := by
  rw [jointMixed_passive_background_wave_identity s₀ F hF g length tau delta target probe iteration,
    passiveOriginalSmallParameter_original_ball_identity B amplitude ha hbuffer b p₀ hp₀ v hv]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointMixed_passive_background_wave_identity
#print axioms GlobalEmbedding.Continuation.jointMixed_passive_background_original_ball
