import NormalPolar.JointMixedBackgroundBallJoint

/-! Genuine external-parameter joint regularity on the unchanged original
open ball. It is manufactured from the one whole-parameter background raw
record, by the actual affine observation and the finite-solver identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {m N p : ℕ} {M S P Tr Λ Β : Type*}
  [TopologicalSpace S] [Subsingleton S]
  [TopologicalSpace P] [T2Space P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin p)) ∞ P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin p)
local notation "X" => Ep × D
local notation "U" => Fin p → ℝ
local notation "IM" => 𝓘(ℝ,D)

theorem jointMixed_passive_background_original_ball_joint
    (s₀ : S) (F : S → M → V) (hF : ∀ s, ContMDiff IM 𝓘(ℝ,V) ∞ (F s))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (length : ℕ) (tau delta : ℝ)
    (target : (s : S) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (probe : U → (s : S) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (iteration n j Rsub Lprimary : ℕ) (horder : j+2+length ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (B : BufferedAtlas P Ep) (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/(‖(EuclideanSpace.equiv (Fin p) ℝ).toContinuousLinearMap‖+1))
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (primary : Λ → Set (P × M)) (e : OpenPartialHomeomorph M D) (Samples : Set X)
    (ell Delta : ℝ) :
    let Fp := fun _ : P => F s₀
    let hFp := fun _ : P => hF s₀
    let gp := passiveParameterPrimary (P := P) s₀ F g
    let input := jointMixedPassiveBackgroundInput s₀ F hF g length tau delta target probe iteration
      (passiveOriginalSmallParameter B amplitude ha b p₀)
    ∀ (raw : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
      reserve Bnd Mg T (fun t => Fp ((B.chart b).symm t)) (fun t => hFp ((B.chart b).symm t))
      (round3ParameterNativePrimary Fp gp (B.chart b))
      (fun t => input ((B.chart b).symm t)) (fun t => input ((B.chart b).symm t))
      (round3ParameterNativeDomain (B.chart b) univ)
      (fun l => round3ParameterNativeDomain (B.chart b) (primary l)) e
      (actualRawObserverOpen e (round3ParameterNativeDomain (B.chart b) univ)) Samples tau ell Delta)
      (geom : ActualOriginalPrimaryPhysicalGeometry
        (fun t => Fp ((B.chart b).symm t)) (fun t => hFp ((B.chart b).symm t))
        (round3ParameterNativePrimary Fp gp (B.chart b))),
    ContDiffOn ℝ ∞ (fun z : U × D => jointMixedSeedBackgroundWave s₀ F hF g
      length tau delta target probe iteration z.1 (e.symm z.2))
      (Metric.ball 0 (actualRepairParameterRadius (tensorChartFamilyOfAtlas B)) ×ˢ e.target) := by
  intro Fp hFp gp input raw geom
  have hs := jointMixed_primary_original_ball_joint_from_raw
    n length j Rsub Lprimary horder reserve Bnd Mg hc hBnd hMg T hT B b p₀ hp₀
    Fp hFp gp (passiveParameterPrimary_chart_preserves s₀ F g) input input
    primary e Samples tau ell Delta raw geom
  apply hs.congr
  intro z hz
  exact (jointMixed_passive_background_original_ball s₀ F hF g length tau delta target probe iteration
    B amplitude ha hbuffer b p₀ hp₀ z.1
    (by simpa only [Metric.mem_ball,dist_zero_right] using hz.1) (e.symm z.2)).symm

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointMixed_passive_background_original_ball_joint
