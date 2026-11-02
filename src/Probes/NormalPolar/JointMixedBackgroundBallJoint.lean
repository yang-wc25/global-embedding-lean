import NormalPolar.JointMixedBackgroundBallIdentity
import Probes.ActualSecondaryPrimaryRawConsumers
import Probes.Round3ParameterPrimaryGlobalNaturality
import Probes.Round3ParameterRawAtlasData
import Probes.ActualIncrementRawObserverDomains

/-! Actual native primitive profiles supply joint smoothness after the true
affine original-ball observation. No external-parameter differentiability
is assumed and no fixed-parameter profile witness is differentiated. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {m N p : ℕ} {M P Tr Λ Β : Type*}
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]
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

theorem jointMixed_primary_original_ball_joint_from_raw
    (n length j Rsub Lprimary : ℕ) (horder : j+2+length ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (B : BufferedAtlas P Ep) (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
    (input inputbar : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (primary : Λ → Set (P × M)) (e : OpenPartialHomeomorph M D) (Samples : Set X)
    (tau ell Delta : ℝ)
    (raw : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
      reserve Bnd Mg T (fun t => F ((B.chart b).symm t)) (fun t => hF ((B.chart b).symm t))
      (round3ParameterNativePrimary F g (B.chart b))
      (fun t => input ((B.chart b).symm t)) (fun t => inputbar ((B.chart b).symm t))
      (round3ParameterNativeDomain (B.chart b) univ)
      (fun l => round3ParameterNativeDomain (B.chart b) (primary l)) e
      (actualRawObserverOpen e (round3ParameterNativeDomain (B.chart b) univ)) Samples tau ell Delta)
    (geom : ActualOriginalPrimaryPhysicalGeometry
      (fun t => F ((B.chart b).symm t)) (fun t => hF ((B.chart b).symm t))
      (round3ParameterNativePrimary F g (B.chart b))) :
    ContDiffOn ℝ ∞
      (fun z : U × D => round3ParameterPrimaryWave F hF g input length tau
        (actualRepairParameterMap (tensorChartFamilyOfAtlas B) b p₀ z.1,e.symm z.2))
      (Metric.ball 0 (actualRepairParameterRadius (tensorChartFamilyOfAtlas B)) ×ˢ e.target) := by
  obtain ⟨CU,CP,hCU,hCP,hbuild⟩ := actual_original_primary_consumers_from_raw
    («Ep» := Ep) (M := M) (Tr := Tr) (Label := Λ) (Sub := Β) (m := m) (N := N)
    n length j Rsub Lprimary horder reserve Bnd Mg hc hBnd hMg T hT
  have hnative := (hbuild
    (fun t => F ((B.chart b).symm t)) (fun t => hF ((B.chart b).symm t))
    (round3ParameterNativePrimary F g (B.chart b))
    (fun t => input ((B.chart b).symm t)) (fun t => inputbar ((B.chart b).symm t))
    (round3ParameterNativeDomain (B.chart b) univ)
    (fun l => round3ParameterNativeDomain (B.chart b) (primary l)) e
    (actualRawObserverOpen e (round3ParameterNativeDomain (B.chart b) univ)) Samples tau ell Delta
    raw geom 1).1
  simp only [one_smul] at hnative
  let coord : U → Ep := fun v => B.chart b p₀+(EuclideanSpace.equiv (Fin p) ℝ).symm v
  let observe : U × D → X := fun z => (coord z.1,z.2)
  have hobs : ContDiff ℝ ∞ observe :=
    (contDiff_const.add ((EuclideanSpace.equiv (Fin p) ℝ).symm.contDiff.comp contDiff_fst)).prodMk
      contDiff_snd
  have hcoord (v : U) (hv : v ∈ Metric.ball 0 (actualRepairParameterRadius (tensorChartFamilyOfAtlas B))) :
      coord v ∈ (B.chart b).target :=
    actualRepairParameter_coordinates_mem_target (tensorChartFamilyOfAtlas B) b p₀ hp₀ v
      (by simpa only [Metric.mem_ball,dist_zero_right] using hv)
  have hmap : MapsTo observe
      (Metric.ball 0 (actualRepairParameterRadius (tensorChartFamilyOfAtlas B)) ×ˢ e.target)
      (actualRawObserverOpen e (round3ParameterNativeDomain (B.chart b) univ)) := by
    intro z hz
    exact ⟨⟨mem_univ _,hz.2⟩,hcoord z.1 hz.1,mem_univ _⟩
  apply (hnative.comp hobs.contDiffOn hmap).congr
  intro z hz
  exact (round3ParameterPrimary_pullback_wave F hF g (B.chart b) hg input length tau
    (coord z.1) (hcoord z.1 hz.1) (e.symm z.2)).symm

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointMixed_primary_original_ball_joint_from_raw
