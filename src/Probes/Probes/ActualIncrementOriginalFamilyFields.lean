import Probes.ActualIncrementOriginalHostFields

/-! Original Data/Core supply the actual cutoff and normal of the SAME
constructed original primary family, including all joint parameter jets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
variable {Β : Type*} [Fintype Β]

theorem actualOriginalPrimaryFamily_cutoff_normal_profiles
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (j : ℕ)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M Es)
    (hdata : ∀ nu beta, ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b nu beta)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu beta))
    (eta : Fin Data.primaryCount → Β → Ep × M → ℝ)
    (hactive : ∀ nu beta w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (nu : Fin Data.primaryCount) (beta : Β) (S : Set X)
    (hS : S ⊆ (b nu beta).target)
    (hsource : (b nu beta).source ⊆ actualOriginalNativeOpen Data (host nu beta,i.2))
    (hsample : MapsTo (b nu beta).symm S ((parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (host nu beta,i.2)))
    (ell budget : ℝ) (hell : 0 < ell)
    (hfinite : incrementsOriginalCoreInputProfile Data j ell ≠ ⊤)
    (hbudget : (incrementsOriginalCoreInputProfile Data j ell).toReal ≤ budget)
    (hinvjet : ∀ k, 1 ≤ k → k ≤ j → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k (b nu beta).symm z‖ ≤ T k) :
    let g := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    let chi := fun z : X => g.cutoff nu (z.1,g.inverse nu beta z.1 z.2)
    let normal := fun z : X => g.normal nu (z.1,g.inverse nu beta z.1 z.2)
    (ContDiffOn ℝ ∞ chi (g.chart nu beta).target ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k chi z‖ ≤
        actualFastChartTransferPrefix T j*(actualOriginalCutoffJetCost (m+1) d j*budget)) ∧
    (ContDiffOn ℝ ∞ normal (g.chart nu beta).target ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k normal z‖ ≤
        actualFastChartTransferPrefix T j*(actualOriginalNormalJetCost (m+1) d N j*budget)) := by
  intro g chi normal
  have hp := actual_original_core_constructed_host_cutoff_normal T hT j Data hd hs
    (host nu beta,i.2) nu (b nu beta) (e nu beta) (hdata nu beta) S hS hsource hsample
    (fun w hw => (hactive nu beta w hw).1) ell budget hell hfinite hbudget hinvjet
  have htarget : (g.chart nu beta).target = (b nu beta).target := (hdata nu beta).1
  rw [htarget]
  exact hp

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualOriginalPrimaryFamily_cutoff_normal_profiles
