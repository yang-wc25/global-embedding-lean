import Probes.Round4ActualProbeBackgroundGeometryLift

/-! Restrict only the passive parameter chart to the actual open parameter
neighborhood. On that neighborhood the complete original finite solver is
unchanged, including every native spatial derivative and the actual mean. -/
noncomputable section
open GlobalEmbedding.Paper Manifold Set
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {P E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

def round4ProbeRestrictedParameterChart (Su : Set P) (hSu : IsOpen Su)
    (a : OpenPartialHomeomorph (Ep×M) (Ep×D)) :
    OpenPartialHomeomorph ((P×Ep)×M) ((P×Ep)×D) :=
  (round4ProbeParameterChartLift a).restrOpen
    ((fun z : (P×Ep)×M => z.1.1) ⁻¹' Su) (hSu.preimage continuous_fst.fst)

theorem round4_restricted_chart_source (Su : Set P) (hSu : IsOpen Su)
    (a : OpenPartialHomeomorph (Ep×M) (Ep×D)) (z : (P×Ep)×M) :
    z ∈ (round4ProbeRestrictedParameterChart Su hSu a).source ↔
      (z.1.2,z.2) ∈ a.source ∧ z.1.1 ∈ Su := by
  change z ∈ (round4ProbeParameterChartLift a).source ∧ z.1.1 ∈ Su ↔ _
  rw [round4ProbeParameterChartLift_mem_source]

theorem round4_restricted_chart_target (Su : Set P) (hSu : IsOpen Su)
    (a : OpenPartialHomeomorph (Ep×M) (Ep×D)) (z : (P×Ep)×D) :
    z ∈ (round4ProbeRestrictedParameterChart Su hSu a).target ↔
      (z.1.2,z.2) ∈ a.target ∧ z.1.1 ∈ Su := by
  change z ∈ (round4ProbeParameterChartLift a).target ∧ z.1.1 ∈ Su ↔ _
  rw [round4ProbeParameterChartLift_mem_target]

def round4PrimaryRestrictedParameterFamily (Su : Set P) (hSu : IsOpen Su)
    (F : Ep → M → V)
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F) :
    IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β)
      (fun t : P×Ep => F t.2) where
  phase nu z := g.phase nu (z.1.2,z.2)
  cutoff nu z := g.cutoff nu (z.1.2,z.2)
  normal nu z := g.normal nu (z.1.2,z.2)
  linearArgument nu t x := g.linearArgument nu t.2 x
  eta nu beta z := g.eta nu beta (z.1.2,z.2)
  chart nu beta := round4ProbeRestrictedParameterChart Su hSu (g.chart nu beta)
  inverse nu beta t x := g.inverse nu beta t.2 x
  normal_mem nu beta z hz := g.normal_mem nu beta (z.1.2,z.2)
    ((round4_restricted_chart_target Su hSu (g.chart nu beta) z).mp hz).1

variable (Su : Set P) (hSu : IsOpen Su)
  (F : Ep → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
  (K : P → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))

theorem round4_restricted_parameter_localFree (tau : ℝ) (nu : Λ) (beta : Β)
    (u : P) (hu : u ∈ Su) (b : Ep) :
    incrementsGlobalPrimaryLocalFree (fun t : P×Ep => F t.2)
      (round4PrimaryRestrictedParameterFamily Su hSu F g) (fun t x => K t.1 t.2 x) tau nu beta (u,b) =
    incrementsGlobalPrimaryLocalFree F g (K u) tau nu beta b := by
  classical
  funext x
  apply Subtype.ext
  have he : ((u,b),x) ∈ (round4ProbeRestrictedParameterChart Su hSu (g.chart nu beta)).target ↔
      (b,x) ∈ (g.chart nu beta).target := by
    rw [round4_restricted_chart_target]; simp only [hu,and_true]
  by_cases hx : (b,x) ∈ (g.chart nu beta).target
  · simp [incrementsGlobalPrimaryLocalFree,round4PrimaryRestrictedParameterFamily,
      incrementsGlobalPrimaryB,hx,he.mpr hx]
    rfl
  · have hn := mt he.mp hx
    simp [incrementsGlobalPrimaryLocalFree,round4PrimaryRestrictedParameterFamily,
      incrementsGlobalPrimaryB,hx,hn]

theorem round4_restricted_parameter_source (tau : ℝ) (nu : Λ) (beta : Β)
    (u : P) (hu : u ∈ Su) (b : Ep) (x : D) :
    incrementsGlobalPrimarySource (fun t : P×Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryRestrictedParameterFamily Su hSu F g) (fun t x => K t.1 t.2 x) tau nu beta ((u,b),x) =
    incrementsGlobalPrimarySource F hF g (K u) tau nu beta (b,x) := by
  unfold incrementsGlobalPrimarySource
  rw [round4_restricted_parameter_localFree Su hSu F g K tau nu beta u hu b]
  rfl

theorem round4_restricted_parameter_finiteU (length : ℕ) (tau : ℝ) (nu : Λ) (beta : Β)
    (u : P) (hu : u ∈ Su) (b : Ep) :
    incrementsGlobalPrimaryFiniteU (fun t : P×Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryRestrictedParameterFamily Su hSu F g) (fun t x => K t.1 t.2 x) length tau nu beta (u,b) =
    incrementsGlobalPrimaryFiniteU F hF g (K u) length tau nu beta b := by
  unfold incrementsGlobalPrimaryFiniteU
  simp only [round4_restricted_parameter_source Su hSu F hF g K tau nu beta u hu]
  rfl

theorem round4_restricted_parameter_localZ (length : ℕ) (tau : ℝ) (ch : Bool) (nu : Λ) (beta : Β)
    (u : P) (hu : u ∈ Su) (b : Ep) (x : D) :
    incrementsGlobalPrimaryLocalZ (fun t : P×Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryRestrictedParameterFamily Su hSu F g) (fun t x => K t.1 t.2 x) length tau ch nu beta ((u,b),x) =
    incrementsGlobalPrimaryLocalZ F hF g (K u) length tau ch nu beta (b,x) := by
  unfold incrementsGlobalPrimaryLocalZ
  rw [round4_restricted_parameter_finiteU Su hSu F hF g K length tau nu beta u hu b,
    round4_restricted_parameter_localFree Su hSu F g K tau nu beta u hu b]
  rfl

theorem round4_restricted_parameter_extension (length : ℕ) (tau : ℝ) (ch : Bool) (nu : Λ) (beta : Β)
    (u : P) (hu : u ∈ Su) (b : Ep) (x : M) :
    incrementsGlobalPrimaryExtension (fun t : P×Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryRestrictedParameterFamily Su hSu F g) (fun t x => K t.1 t.2 x) length tau ch nu beta ((u,b),x) =
    incrementsGlobalPrimaryExtension F hF g (K u) length tau ch nu beta (b,x) := by
  classical
  unfold incrementsGlobalPrimaryExtension
  change (if ((u,b),x) ∈ (round4ProbeRestrictedParameterChart Su hSu (g.chart nu beta)).source then
    incrementsGlobalPrimaryLocalZ (fun t : P×Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryRestrictedParameterFamily Su hSu F g) (fun t x => K t.1 t.2 x) length tau ch nu beta
      (round4ProbeParameterChartLift (g.chart nu beta) ((u,b),x)) else 0) = _
  rw [round4_restricted_chart_source]
  simp only [hu,and_true,round4ProbeParameterChartLift_apply,
    round4_restricted_parameter_localZ Su hSu F hF g K length tau ch nu beta u hu]

theorem round4_restricted_parameter_amplitude (length : ℕ) (tau : ℝ) (ch : Bool) (nu : Λ)
    (u : P) (hu : u ∈ Su) (b : Ep) (x : M) :
    incrementsGlobalPrimaryAmplitude (fun t : P×Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryRestrictedParameterFamily Su hSu F g) (fun t x => K t.1 t.2 x) length tau ch nu ((u,b),x) =
    incrementsGlobalPrimaryAmplitude F hF g (K u) length tau ch nu (b,x) := by
  simp only [incrementsGlobalPrimaryAmplitude,
    round4_restricted_parameter_extension Su hSu F hF g K length tau ch nu _ u hu]

theorem round4_restricted_parameter_coefficient (length : ℕ) (tau : ℝ) (ch : Bool) (nu : Λ)
    (u : P) (hu : u ∈ Su) (b : Ep) (x : M) :
    incrementsGlobalPrimaryCoefficient (fun t : P×Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryRestrictedParameterFamily Su hSu F g) (fun t x => K t.1 t.2 x) length tau ch nu ((u,b),x) =
    incrementsGlobalPrimaryCoefficient F hF g (K u) length tau ch nu (b,x) := by
  have hd (ch : Bool) : incrementsGlobalSpatialDerivative (I := I)
      (incrementsGlobalPrimaryAmplitude (fun t : P×Ep => F t.2) (fun t => hF t.2)
        (round4PrimaryRestrictedParameterFamily Su hSu F g) (fun t x => K t.1 t.2 x)
          length tau ch nu) ((u,b),x) =
      incrementsGlobalSpatialDerivative (I := I)
        (incrementsGlobalPrimaryAmplitude F hF g (K u) length tau ch nu) (b,x) := by
    have he : (fun y => incrementsGlobalPrimaryAmplitude
        (fun t : P×Ep => F t.2) (fun t => hF t.2)
        (round4PrimaryRestrictedParameterFamily Su hSu F g) (fun t x => K t.1 t.2 x)
          length tau ch nu ((u,b),y)) =
        (fun y => incrementsGlobalPrimaryAmplitude F hF g (K u) length tau ch nu (b,y)) := by
      funext y
      exact round4_restricted_parameter_amplitude Su hSu F hF g K length tau ch nu u hu b y
    exact congrArg (fun f : M → V =>
      (tangentSpaceCastModel 𝓘(ℝ,V) (f x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ,V) f x)) he
  simp only [incrementsGlobalPrimaryCoefficient,hd,
    round4_restricted_parameter_amplitude Su hSu F hF g K length tau _ nu u hu b x]
  rfl

theorem round4_restricted_parameter_mean (length : ℕ) (tau : ℝ)
    (u : P) (hu : u ∈ Su) (b : Ep) (x : M) :
    incrementsGlobalPrimaryMean (fun t : P×Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryRestrictedParameterFamily Su hSu F g) (fun t x => K t.1 t.2 x) length tau (u,b) x =
    incrementsGlobalPrimaryMean F hF g (K u) length tau b x := by
  simp only [incrementsGlobalPrimaryMean,
    round4_restricted_parameter_coefficient Su hSu F hF g K length tau _ _ u hu b x]


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_restricted_parameter_amplitude

#print axioms GlobalEmbedding.Continuation.round4_restricted_parameter_mean
