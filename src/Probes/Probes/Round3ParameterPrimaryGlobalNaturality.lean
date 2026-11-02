import Probes.Round3ParameterPrimaryPullback

/-! A single physical primary wave and actual mean in every parameter chart.
All equalities are for the same finite length and input tensor; no chartwise
choice of an output and no re-cutting of a constructed output is involved. -/

noncomputable section
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {E H M P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P] [TopologicalSpace Q]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
  (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ p, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
  (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
  (B : OpenPartialHomeomorph P Q)
  (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
  (length : ℕ) (tau : ℝ)
include hg

theorem round3ParameterPrimary_pullback_extension
    (ch : Bool) (ν : Λ) (β : Β) (t : Q) (ht : t ∈ B.target) (x : M) :
    round3ParameterPrimaryExtension (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau ch ν β (t,x) =
      round3ParameterPrimaryExtension F hF g input length tau ch ν β (B.symm t,x) := by
  classical
  have hi := round3ParameterChartPullback_source_iff B (g.chart ν β) (hg ν β) (t,x) ht
  by_cases hx : (B.symm t,x) ∈ (g.chart ν β).source
  · have hb := hi.mpr hx
    have ha : round3ParameterChartPullback B (g.chart ν β) (t,x) =
        (t,(g.chart ν β (B.symm t,x)).2) := by
      rw [round3ParameterChartPullback_apply, hg ν β _ hx]
      simp only [B.right_inv ht]
    have hc : g.chart ν β (B.symm t,x) =
        (B.symm t,(g.chart ν β (B.symm t,x)).2) := Prod.ext (hg ν β _ hx) rfl
    simp only [round3ParameterPrimaryExtension]
    change (if (t,x) ∈ (round3ParameterChartPullback B (g.chart ν β)).source then _ else 0) = _
    rw [if_pos hb, if_pos hx]
    change round3ParameterPrimaryLocalZ _ _ _ _ _ _ _ _ _
      (round3ParameterChartPullback B (g.chart ν β) (t,x)) = _
    rw [ha, round3ParameterPrimary_pullback_localZ F hF g B hg input length tau ch ν β t ht, hc]
  · have hb := mt hi.mp hx
    simp only [round3ParameterPrimaryExtension]
    change (if (t,x) ∈ (round3ParameterChartPullback B (g.chart ν β)).source then _ else 0) = _
    rw [if_neg hb, if_neg hx]

theorem round3ParameterPrimary_pullback_amplitude
    (ch : Bool) (ν : Λ) (t : Q) (ht : t ∈ B.target) (x : M) :
    round3ParameterPrimaryAmplitude (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau ch ν (t,x) =
      round3ParameterPrimaryAmplitude F hF g input length tau ch ν (B.symm t,x) := by
  unfold round3ParameterPrimaryAmplitude
  exact Finset.sum_congr rfl (fun β _ =>
    round3ParameterPrimary_pullback_extension F hF g B hg input length tau ch ν β t ht x)

theorem round3ParameterPrimary_pullback_wave
    (t : Q) (ht : t ∈ B.target) (x : M) :
    round3ParameterPrimaryWave (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau (t,x) =
      round3ParameterPrimaryWave F hF g input length tau (B.symm t,x) := by
  unfold round3ParameterPrimaryWave
  apply Finset.sum_congr rfl
  intro ν _
  rw [round3ParameterPrimary_pullback_amplitude F hF g B hg input length tau true ν t ht,
    round3ParameterPrimary_pullback_amplitude F hF g B hg input length tau false ν t ht]
  rfl

theorem round3ParameterPrimary_pullback_coefficient
    (ch : Bool) (ν : Λ) (t : Q) (ht : t ∈ B.target) (x : M) :
    round3ParameterPrimaryCoefficient (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau ch ν (t,x) =
      round3ParameterPrimaryCoefficient F hF g input length tau ch ν (B.symm t,x) := by
  have ha (b : Bool) := funext (round3ParameterPrimary_pullback_amplitude F hF g B hg input length tau b ν t ht)
  unfold round3ParameterPrimaryCoefficient incrementsGlobalSpatialDerivative incrementsGlobalScalarDerivative
  dsimp only
  rw [ha ch]
  simp only [round3ParameterPrimary_pullback_amplitude F hF g B hg input length tau ch ν t ht,
    round3ParameterPrimary_pullback_amplitude F hF g B hg input length tau (!ch) ν t ht]
  rfl

theorem round3ParameterPrimary_pullback_mean
    (t : Q) (ht : t ∈ B.target) (x : M) :
    round3ParameterPrimaryMean (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau t x =
      round3ParameterPrimaryMean F hF g input length tau (B.symm t) x := by
  unfold round3ParameterPrimaryMean
  simp only [round3ParameterPrimary_pullback_coefficient F hF g B hg input length tau true,
    round3ParameterPrimary_pullback_coefficient F hF g B hg input length tau false, ht]

theorem round3ParameterPrimary_pullback_meanError
    (t : Q) (ht : t ∈ B.target) (x : M) :
    round3ParameterPrimaryMeanError (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau t x =
      round3ParameterPrimaryMeanError F hF g input length tau (B.symm t) x := by
  unfold round3ParameterPrimaryMeanError
  rw [round3ParameterPrimary_pullback_mean F hF g B hg input length tau t ht]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterPrimary_pullback_wave
#print axioms GlobalEmbedding.Continuation.round3ParameterPrimary_pullback_meanError
