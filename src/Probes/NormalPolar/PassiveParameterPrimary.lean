import NormalPolar.PassiveParameterChart
import Probes.Round3ParameterPrimaryNative

/-!
# The original primary solver with a passive parameter

All primitive fields are lifted from a one-point seed parameter space.
The actual finite solver is retained.  The identities below are proved from
its source and reconstruction, before any background iterate or first map is
formed.  The seed may be the original zero-dimensional Euclidean family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M S P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace S] [Subsingleton S]
  [TopologicalSpace P] {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
variable (s₀ : S) (F : S → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ s, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F s))
  (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)

/-- Original primitive fields and the actual product chart. -/
def passiveParameterPrimary :
    Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β)
      (fun _ : P => F s₀) where
  phase := fun ν z => g.phase ν (s₀,z.2)
  cutoff := fun ν z => g.cutoff ν (s₀,z.2)
  normal := fun ν z => g.normal ν (s₀,z.2)
  linearArgument := fun ν _ x => g.linearArgument ν s₀ x
  eta := fun ν β z => g.eta ν β (s₀,z.2)
  chart := fun ν β => passiveParameterChart s₀ (g.chart ν β)
  inverse := fun ν β _ => g.inverse ν β s₀
  normal_mem := fun ν β z hz => g.normal_mem ν β (s₀,z.2) hz

theorem passiveParameterPrimary_chart_preserves (ν : Λ) (β : Β) :
    Round3ParameterChartPreserves ((passiveParameterPrimary (P:=P) s₀ F g).chart ν β) :=
  passiveParameterChart_preserves s₀ (g.chart ν β)

variable (input : (s : S) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
  (length : ℕ) (tau : ℝ)

theorem passiveParameterPrimary_localFree (ν : Λ) (β : Β) (b : P)
    (x : EuclideanSpace ℝ (Fin (m+1))) :
    round3ParameterPrimaryLocalFree (fun _ : P => F s₀)
      (passiveParameterPrimary s₀ F g) (fun _ => input s₀) tau ν β b x =
    round3ParameterPrimaryLocalFree F g input tau ν β s₀ x := by
  classical
  simp only [round3ParameterPrimaryLocalFree, passiveParameterPrimary,
    passiveParameterChart_target, round3ParameterPrimaryB]

theorem passiveParameterPrimary_source (ν : Λ) (β : Β) (b : P)
    (x : EuclideanSpace ℝ (Fin (m+1))) :
    round3ParameterPrimarySource (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) (fun _ => input s₀) tau ν β (b,x) =
    round3ParameterPrimarySource F hF g input tau ν β (s₀,x) := by
  have hf := funext (passiveParameterPrimary_localFree s₀ F g input tau ν β b)
  unfold round3ParameterPrimarySource
  rw [hf]
  rfl

theorem passiveParameterPrimary_finiteU (ν : Λ) (β : Β) (b : P) :
    round3ParameterPrimaryFiniteU (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) (fun _ => input s₀) length tau ν β b =
    round3ParameterPrimaryFiniteU F hF g input length tau ν β s₀ := by
  unfold round3ParameterPrimaryFiniteU
  have hs := funext (passiveParameterPrimary_source s₀ F hF g input tau ν β b)
  rw [hs]
  rfl

theorem passiveParameterPrimary_localZ (ch : Bool) (ν : Λ) (β : Β) (b : P)
    (x : EuclideanSpace ℝ (Fin (m+1))) :
    round3ParameterPrimaryLocalZ (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) (fun _ => input s₀) length tau ch ν β (b,x) =
    round3ParameterPrimaryLocalZ F hF g input length tau ch ν β (s₀,x) := by
  unfold round3ParameterPrimaryLocalZ
  rw [passiveParameterPrimary_finiteU s₀ F hF g input length tau ν β b]
  have hf := funext (passiveParameterPrimary_localFree s₀ F g input tau ν β b)
  simp only [hf]
  rfl

theorem passiveParameterPrimary_extension (ch : Bool) (ν : Λ) (β : Β) (b : P) (x : M) :
    round3ParameterPrimaryExtension (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) (fun _ => input s₀) length tau ch ν β (b,x) =
    round3ParameterPrimaryExtension F hF g input length tau ch ν β (s₀,x) := by
  classical
  have ha : g.chart ν β (s₀,x) = (s₀,(g.chart ν β (s₀,x)).2) :=
    Prod.ext (Subsingleton.elim _ _) rfl
  unfold round3ParameterPrimaryExtension
  change (if (s₀,x) ∈ (g.chart ν β).source then _ else 0) = _
  split_ifs with hx
  · change round3ParameterPrimaryLocalZ _ _ _ _ _ _ _ _ _
      (b,(g.chart ν β (s₀,x)).2) = _
    rw [ha]
    exact passiveParameterPrimary_localZ s₀ F hF g input length tau ch ν β b _
  · rfl

theorem passiveParameterPrimary_amplitude (ch : Bool) (ν : Λ) (b : P) (x : M) :
    round3ParameterPrimaryAmplitude (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) (fun _ => input s₀) length tau ch ν (b,x) =
    round3ParameterPrimaryAmplitude F hF g input length tau ch ν (s₀,x) := by
  unfold round3ParameterPrimaryAmplitude
  exact Finset.sum_congr rfl (fun β _ =>
    passiveParameterPrimary_extension s₀ F hF g input length tau ch ν β b x)

theorem passiveParameterPrimary_wave (b : P) (x : M) :
    round3ParameterPrimaryWave (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) (fun _ => input s₀) length tau (b,x) =
    round3ParameterPrimaryWave F hF g input length tau (s₀,x) := by
  unfold round3ParameterPrimaryWave
  apply Finset.sum_congr rfl
  intro ν _
  rw [passiveParameterPrimary_amplitude s₀ F hF g input length tau true ν b x,
    passiveParameterPrimary_amplitude s₀ F hF g input length tau false ν b x]
  rfl

theorem passiveParameterPrimary_coefficient (ch : Bool) (ν : Λ) (b : P) (x : M) :
    round3ParameterPrimaryCoefficient (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) (fun _ => input s₀) length tau ch ν (b,x) =
    round3ParameterPrimaryCoefficient F hF g input length tau ch ν (s₀,x) := by
  have ha (c : Bool) := funext
    (passiveParameterPrimary_amplitude s₀ F hF g input length tau c ν b)
  unfold round3ParameterPrimaryCoefficient incrementsGlobalSpatialDerivative
    incrementsGlobalScalarDerivative
  dsimp only
  rw [ha ch]
  simp only [passiveParameterPrimary_amplitude s₀ F hF g input length tau ch ν b x,
    passiveParameterPrimary_amplitude s₀ F hF g input length tau (!ch) ν b x]
  rfl

theorem passiveParameterPrimary_mean (b : P) (x : M) :
    round3ParameterPrimaryMean (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) (fun _ => input s₀) length tau b x =
    round3ParameterPrimaryMean F hF g input length tau s₀ x := by
  simp only [round3ParameterPrimaryMean,
    passiveParameterPrimary_coefficient s₀ F hF g input length tau true,
    passiveParameterPrimary_coefficient s₀ F hF g input length tau false]

theorem passiveParameterPrimary_meanError (b : P) (x : M) :
    round3ParameterPrimaryMeanError (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) (fun _ => input s₀) length tau b x =
    round3ParameterPrimaryMeanError F hF g input length tau s₀ x := by
  unfold round3ParameterPrimaryMeanError
  rw [passiveParameterPrimary_mean s₀ F hF g input length tau b x]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveParameterPrimary
#print axioms GlobalEmbedding.Continuation.passiveParameterPrimary_wave
#print axioms GlobalEmbedding.Continuation.passiveParameterPrimary_meanError

