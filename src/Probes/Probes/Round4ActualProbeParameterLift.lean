import GlobalEmbedding.Paper.IncrementsGlobalPrimaryMeanBinding
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Exact external-parameter naturality of the original full-field solver

An extra parameter is lifted through the actual joint charts by the ordinary
product chart. All source-only derivatives in the finite solver remain literal
native spatial derivatives. The final identity compares the original solver
on the augmented parameter space with the original solver applied to the whole
spatial field at each fixed external parameter. This is not evaluation of the
solver at a pointwise tensor value.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

variable {P E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The original joint chart with one passive external parameter. -/
def round4ProbeParameterChartLift
    (a : OpenPartialHomeomorph (Ep × M) (Ep × D)) :
    OpenPartialHomeomorph ((P × Ep) × M) ((P × Ep) × D) :=
  (Homeomorph.prodAssoc P Ep M).toOpenPartialHomeomorph.trans
    (((OpenPartialHomeomorph.refl P).prod a).trans
      (Homeomorph.prodAssoc P Ep D).symm.toOpenPartialHomeomorph)

theorem round4ProbeParameterChartLift_apply
    (a : OpenPartialHomeomorph (Ep × M) (Ep × D)) (u : P) (b : Ep) (x : M) :
    round4ProbeParameterChartLift (P := P) a ((u,b),x) =
      ((u,(a (b,x)).1),(a (b,x)).2) := rfl

theorem round4ProbeParameterChartLift_mem_source
    (a : OpenPartialHomeomorph (Ep × M) (Ep × D)) (z : (P × Ep) × M) :
    z ∈ (round4ProbeParameterChartLift (P := P) a).source ↔ (z.1.2,z.2) ∈ a.source := by
  simp [round4ProbeParameterChartLift]
  rfl

theorem round4ProbeParameterChartLift_mem_target
    (a : OpenPartialHomeomorph (Ep × M) (Ep × D)) (z : (P × Ep) × D) :
    z ∈ (round4ProbeParameterChartLift (P := P) a).target ↔ (z.1.2,z.2) ∈ a.target := by
  simp [round4ProbeParameterChartLift]
  rfl

/-- The SAME original primitive family, independent of the added parameter. -/
def round4PrimaryFamilyParameterLift
    (F : Ep → M → V)
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F) :
    IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β)
      (fun t : P × Ep => F t.2) where
  phase ν z := g.phase ν (z.1.2,z.2)
  cutoff ν z := g.cutoff ν (z.1.2,z.2)
  normal ν z := g.normal ν (z.1.2,z.2)
  linearArgument ν t x := g.linearArgument ν t.2 x
  eta ν β z := g.eta ν β (z.1.2,z.2)
  chart ν β := round4ProbeParameterChartLift (P := P) (g.chart ν β)
  inverse ν β t x := g.inverse ν β t.2 x
  normal_mem ν β z hz := g.normal_mem ν β (z.1.2,z.2)
    ((round4ProbeParameterChartLift_mem_target (g.chart ν β) z).mp hz)

theorem round4_primary_parameter_lift_localFree
    (F : Ep → M → V)
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (K : P → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (tau : ℝ) (ν : Λ) (β : Β) (u : P) (b : Ep) :
    incrementsGlobalPrimaryLocalFree (fun t : P × Ep => F t.2)
      (round4PrimaryFamilyParameterLift F g) (fun t x => K t.1 t.2 x) tau ν β (u,b) =
      incrementsGlobalPrimaryLocalFree F g (K u) tau ν β b := by
  classical
  funext x
  apply Subtype.ext
  by_cases hx : (b,x) ∈ (g.chart ν β).target
  · have hl := (round4ProbeParameterChartLift_mem_target (P := P) (g.chart ν β) ((u,b),x)).mpr hx
    simp [incrementsGlobalPrimaryLocalFree,round4PrimaryFamilyParameterLift,
      incrementsGlobalPrimaryB,hx,hl]
    rfl
  · have hl : ((u,b),x) ∉ (round4ProbeParameterChartLift (P := P) (g.chart ν β)).target := by
      simpa only [round4ProbeParameterChartLift_mem_target] using hx
    simp [incrementsGlobalPrimaryLocalFree,round4PrimaryFamilyParameterLift,
      incrementsGlobalPrimaryB,hx,hl]

theorem round4_primary_parameter_lift_source
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (K : P → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (tau : ℝ) (ν : Λ) (β : Β) (u : P) (b : Ep) (x : D) :
    incrementsGlobalPrimarySource (fun t : P × Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryFamilyParameterLift F g) (fun t x => K t.1 t.2 x) tau ν β ((u,b),x) =
      incrementsGlobalPrimarySource F hF g (K u) tau ν β (b,x) := by
  unfold incrementsGlobalPrimarySource
  rw [round4_primary_parameter_lift_localFree]
  rfl

theorem round4_primary_parameter_lift_finiteU
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (K : P → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (ν : Λ) (β : Β) (u : P) (b : Ep) :
    incrementsGlobalPrimaryFiniteU (fun t : P × Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryFamilyParameterLift F g) (fun t x => K t.1 t.2 x) length tau ν β (u,b) =
      incrementsGlobalPrimaryFiniteU F hF g (K u) length tau ν β b := by
  unfold incrementsGlobalPrimaryFiniteU
  simp only [round4_primary_parameter_lift_source]
  rfl

theorem round4_primary_parameter_lift_localZ
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (K : P → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (ch : Bool) (ν : Λ) (β : Β) (u : P) (b : Ep) (x : D) :
    incrementsGlobalPrimaryLocalZ (fun t : P × Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryFamilyParameterLift F g) (fun t x => K t.1 t.2 x) length tau ch ν β ((u,b),x) =
      incrementsGlobalPrimaryLocalZ F hF g (K u) length tau ch ν β (b,x) := by
  unfold incrementsGlobalPrimaryLocalZ
  rw [round4_primary_parameter_lift_finiteU,round4_primary_parameter_lift_localFree]
  rfl

theorem round4_primary_parameter_lift_extension
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (K : P → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (ch : Bool) (ν : Λ) (β : Β) (u : P) (b : Ep) (x : M) :
    incrementsGlobalPrimaryExtension (fun t : P × Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryFamilyParameterLift F g) (fun t x => K t.1 t.2 x) length tau ch ν β ((u,b),x) =
      incrementsGlobalPrimaryExtension F hF g (K u) length tau ch ν β (b,x) := by
  classical
  unfold incrementsGlobalPrimaryExtension
  change (if ((u,b),x) ∈ (round4ProbeParameterChartLift (P := P) (g.chart ν β)).source then
    incrementsGlobalPrimaryLocalZ (fun t : P × Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryFamilyParameterLift F g) (fun t x => K t.1 t.2 x) length tau ch ν β
      (round4ProbeParameterChartLift (P := P) (g.chart ν β) ((u,b),x)) else 0) = _
  rw [round4ProbeParameterChartLift_mem_source,round4ProbeParameterChartLift_apply,
    round4_primary_parameter_lift_localZ]


theorem round4_primary_parameter_lift_amplitude
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (K : P → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (ch : Bool) (ν : Λ) (u : P) (b : Ep) (x : M) :
    incrementsGlobalPrimaryAmplitude (fun t : P × Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryFamilyParameterLift F g) (fun t x => K t.1 t.2 x) length tau ch ν ((u,b),x) =
      incrementsGlobalPrimaryAmplitude F hF g (K u) length tau ch ν (b,x) := by
  simp only [incrementsGlobalPrimaryAmplitude,round4_primary_parameter_lift_extension]

theorem round4_primary_parameter_lift_coefficient
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (K : P → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (ch : Bool) (ν : Λ) (u : P) (b : Ep) (x : M) :
    incrementsGlobalPrimaryCoefficient (fun t : P × Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryFamilyParameterLift F g) (fun t x => K t.1 t.2 x) length tau ch ν ((u,b),x) =
      incrementsGlobalPrimaryCoefficient F hF g (K u) length tau ch ν (b,x) := by
  have hd (ch : Bool) : incrementsGlobalSpatialDerivative (I := I)
      (incrementsGlobalPrimaryAmplitude (fun t : P × Ep => F t.2) (fun t => hF t.2)
        (round4PrimaryFamilyParameterLift F g) (fun t x => K t.1 t.2 x) length tau ch ν) ((u,b),x) =
      incrementsGlobalSpatialDerivative (I := I)
        (incrementsGlobalPrimaryAmplitude F hF g (K u) length tau ch ν) (b,x) := by
    have he : (fun y => incrementsGlobalPrimaryAmplitude
        (fun t : P × Ep => F t.2) (fun t => hF t.2) (round4PrimaryFamilyParameterLift F g)
        (fun t x => K t.1 t.2 x) length tau ch ν ((u,b),y)) =
        (fun y => incrementsGlobalPrimaryAmplitude F hF g (K u) length tau ch ν (b,y)) := by
      funext y
      exact round4_primary_parameter_lift_amplitude F hF g K length tau ch ν u b y
    exact congrArg (fun f : M → V =>
      (tangentSpaceCastModel 𝓘(ℝ,V) (f x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ,V) f x)) he
  simp only [incrementsGlobalPrimaryCoefficient,hd,round4_primary_parameter_lift_amplitude]
  rfl

/-- The augmented-parameter original mean is the original whole-field mean
of each fixed-parameter input slice, with every spatial derivative retained. -/
theorem round4_primary_parameter_lift_mean
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (K : P → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (u : P) (b : Ep) (x : M) :
    incrementsGlobalPrimaryMean (fun t : P × Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryFamilyParameterLift F g) (fun t x => K t.1 t.2 x) length tau (u,b) x =
      incrementsGlobalPrimaryMean F hF g (K u) length tau b x := by
  simp only [incrementsGlobalPrimaryMean,round4_primary_parameter_lift_coefficient]

theorem round4_primary_parameter_lift_mean_error
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (K : P → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (u : P) :
    (fun b x => incrementsGlobalPrimaryMeanError (fun t : P × Ep => F t.2) (fun t => hF t.2)
      (round4PrimaryFamilyParameterLift F g) (fun t x => K t.1 t.2 x) length tau (u,b) x) =
      incrementsGlobalPrimaryMeanError F hF g (K u) length tau := by
  funext b x
  simp only [incrementsGlobalPrimaryMeanError,round4_primary_parameter_lift_mean]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4_primary_parameter_lift_source
#print axioms GlobalEmbedding.Continuation.round4_primary_parameter_lift_finiteU
#print axioms GlobalEmbedding.Continuation.round4_primary_parameter_lift_extension

#print axioms GlobalEmbedding.Continuation.round4_primary_parameter_lift_mean_error
