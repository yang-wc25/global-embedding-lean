import Smoothing.ParameterRound2MeanPrimitives
import Probes.ActualIncrementPrimaryCoefficientBinding

/-! The SAME physical primary coefficient has no support beyond its genuine
relative primary cutoff support. Inactive labels require no phase smoothness.
This is used with the product of the two coefficients in the quadratic source;
the ordinary secondary partition is not required to vanish on a pair boundary. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

variable (F : Ep → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ p, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
  (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
  (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
  (q : ℕ) (hq : 1 ≤ q) (tau delta : ℝ) (htau : 0 < tau)
  (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
  (h : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
  (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m+1))))
  (he : ContMDiffOn I 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ e e.source)
  (heInv : ContMDiffOn 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) I ∞ e.symm e.target)

include hq htau h he heInv

 theorem actual_original_physical_coefficient_inactive_on
    (Omega : Set X) (hOmega : IsOpen Omega)
    (hTarget : ∀ z ∈ Omega, z.2 ∈ e.target)
    (hMap : MapsTo (fun z : X => (z.1,e.symm z.2)) Omega W)
    (z : X) (hz : z ∈ Omega) (nu : Λ)
    (hinactive : (z.1,e.symm z.2) ∉ incrementsGlobalRelativeSupport W (g.cutoff nu)) :
    (fun w : X => incrementsSecondaryPhysicalCoefficient
      (fun mu b x => g.phase mu (b,e.symm x)) tau (fun _ _ _ _ => 1)
      (fun mu b beta x => delta • incrementsGlobalPrimaryExtension F hF g input (q+2) tau true mu beta (b,e.symm x))
      (fun mu b beta x => delta • incrementsGlobalPrimaryExtension F hF g input (q+2) tau false mu beta (b,e.symm x))
      (fun r _ => EuclideanSpace.single r 1) w nu) =ᶠ[𝓝 z] 0 := by
  have hbind := increments_global_primary_mean_binding F hF g input q hq tau htau
    W h.hW primary h.hPrimary h.hPrimarySupport h.hSourceW h.hChart h.hChartInv h.hInverse
    h.hCombinedSupport h.hPhase h.hCut h.hNormal h.hArgument h.hEta h.hPositive h.hUnit
    h.hPartition h.hSymm h.hDecomp h.hDouble h.hInteraction h.hG h.hJ h.hT0 h.hA h.hB h.hSecond
  have hkappa : ContinuousOn (fun w : X => (w.1,e.symm w.2)) Omega :=
    continuousOn_fst.prodMk (e.symm.continuousOn.comp continuousOn_snd hTarget)
  have hzero := parameterRound2_actual_globalObserved_inactive_germ F hF g input (q+2) tau
    W h.hW nu (h.hCombinedSupport nu) (h.hInverse nu) e Omega hOmega hkappa hMap z hz hinactive
  filter_upwards [hOmega.mem_nhds hz,hzero.1,hzero.2] with w hw hwL hwE
  rw [actual_original_primary_physical_coefficient_binding]
  have heq := congrFun (hbind.2.2 e he heInv w.1 w.2 (hTarget w hw) (hMap hw)).1 nu
  rw [heq]
  change delta • (incrementsGlobalObservedLeading F g input e w.1 w.2 nu +
    incrementsGlobalObservedError F hF g input (q+2) tau e w.1 w.2 nu) = 0
  simp only [hwL,hwE,Pi.zero_apply,add_zero,smul_zero]

 theorem actual_original_physical_coefficient_support_on
    (Omega : Set X) (hOmega : IsOpen Omega)
    (hTarget : ∀ z ∈ Omega, z.2 ∈ e.target)
    (hMap : MapsTo (fun z : X => (z.1,e.symm z.2)) Omega W)
    (z : X) (hz : z ∈ Omega) (nu : Λ)
    (hsupport : z ∈ tsupport (fun w : X => incrementsSecondaryPhysicalCoefficient
      (fun mu b x => g.phase mu (b,e.symm x)) tau (fun _ _ _ _ => 1)
      (fun mu b beta x => delta • incrementsGlobalPrimaryExtension F hF g input (q+2) tau true mu beta (b,e.symm x))
      (fun mu b beta x => delta • incrementsGlobalPrimaryExtension F hF g input (q+2) tau false mu beta (b,e.symm x))
      (fun r _ => EuclideanSpace.single r 1) w nu)) :
    (z.1,e.symm z.2) ∈ incrementsGlobalRelativeSupport W (g.cutoff nu) := by
  by_contra hn
  exact (notMem_tsupport_iff_eventuallyEq.mpr
    (actual_original_physical_coefficient_inactive_on F hF g input q hq tau delta htau W primary h
      e he heInv Omega hOmega hTarget hMap z hz nu hn)) hsupport

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_physical_coefficient_inactive_on
#print axioms GlobalEmbedding.Continuation.actual_original_physical_coefficient_support_on
