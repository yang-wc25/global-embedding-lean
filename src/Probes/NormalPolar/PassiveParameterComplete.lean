import NormalPolar.PassiveParameterBackground
import NormalPolar.PassiveParameterSecondary
import NormalPolar.ParameterDisplacementCompleteIteratedSources

/-!
# One complete first increment on every passive parameter space

Every ordered signed secondary source is formed from the actual complete
primary amplitudes at the same finite background iterate.  The equality with
the single-point seed is proved from the primitive lift, including both
inverse-coordinate Jacobians and all subordinate terms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {M S P Λ Β SubSecondary : Type*}
  [TopologicalSpace S] [Subsingleton S] [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))

variable (s₀ : S) (F : S → M → (EuclideanSpace ℝ (Fin N))) (hF : ∀ s, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,(EuclideanSpace ℝ (Fin N))) ∞ (F s))
  (g : Round3ParameterPrimaryFamily (I:=𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (m:=m) (Λ:=Λ) (Β:=Β) F)
  (label : (Fin r × Bool) ↪ Fin p)
  (c : Fin r → S → (EuclideanSpace ℝ (Fin (m+1))) → M)
  (vf : (l : Fin r) → (s : S) → (x : (EuclideanSpace ℝ (Fin (m+1)))) → normalSpace (I:=𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (F s) (c l s x))
  (phase : Fin r → S × M → ℝ) (tau delta : ℝ)
  (backgroundLength probeLength secondaryLength : ℕ)
  (a : Fin r → OpenPartialHomeomorph (S × M) (S × (EuclideanSpace ℝ (Fin (m+1)))))
  (target : (s : S) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (iteration : ℕ)

theorem passiveParameterComplete_secondary_piece
    (u : Fin p → ℝ) (rec : ((Λ ⊕ Fin r) × (Λ ⊕ Fin r)) × Fin 4)
    (choice : Round3ParameterSecondaryChoice S M m)
    (hc : Round3ParameterChartPreserves choice.chart) (b : P) (x : M) :
    (actualParameterProbeIteratedSecondarySource
      (fun _ : P => F s₀) (fun _ => hF s₀) (passiveParameterPrimary s₀ F g)
      label (fun l _ => c l s₀) (fun l _ => vf l s₀)
      (fun l z => phase l (s₀,z.2)) tau delta backgroundLength probeLength
      (fun l => passiveParameterChart s₀ (a l)) (fun _ => target s₀) iteration u rec
      (passiveParameterSecondaryChoice s₀ choice)
      (passiveParameterSecondaryChoice_preserves s₀ choice)).wave
      (fun _ : P => F s₀) (fun _ => hF s₀) tau secondaryLength (b,x) =
    (actualParameterProbeIteratedSecondarySource F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration u rec choice hc).wave
      F hF tau secondaryLength (s₀,x) := by
  have hp : Sum.elim (passiveParameterPrimary (P:=P) s₀ F g).phase
      (fun l z => phase l (s₀,z.2)) =
      fun l (z : P × M) => Sum.elim g.phase phase l (s₀,z.2) := by
    funext l z
    cases l <;> rfl
  have hA (imag : Bool) :
      actualParameterProbeIteratedAmplitude
        (fun _ : P => F s₀) (fun _ => hF s₀) (passiveParameterPrimary s₀ F g)
        label (fun l _ => c l s₀) (fun l _ => vf l s₀)
        (fun l z => phase l (s₀,z.2)) tau delta backgroundLength probeLength
        (fun l => passiveParameterChart s₀ (a l)) (fun _ => target s₀) iteration u imag =
      fun l (z : P × M) => actualParameterProbeIteratedAmplitude F hF g label c vf phase
        tau delta backgroundLength probeLength a target iteration u imag l (s₀,z.2) := by
    funext l z
    exact passiveParameterBackground_complete_amplitude s₀ F hF g backgroundLength tau delta target
      label c vf phase probeLength a iteration u imag l z.1 z.2
  unfold actualParameterProbeIteratedSecondarySource
  rw [hp,hA false,hA true]
  exact passiveParameterSecondary_primary_wave s₀ F hF (Sum.elim g.phase phase) _ _
    tau rec choice hc secondaryLength b x

variable
  (choice : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary → Round3ParameterSecondaryChoice S M m)
  (hc : ∀ rec k, Round3ParameterChartPreserves (choice rec k).chart)

/-- The complete first increment, with the same labels, finite lengths and
actual background recurrence, agrees at every passive parameter point. -/
theorem passiveParameterComplete_increment (u : Fin p → ℝ) (b : P) (x : M) :
    actualParameterCompleteFirstIncrementFromChoices
      (fun _ : P => F s₀) (fun _ => hF s₀) (passiveParameterPrimary s₀ F g)
      label (fun l _ => c l s₀) (fun l _ => vf l s₀)
      (fun l z => phase l (s₀,z.2)) tau delta backgroundLength probeLength secondaryLength
      (fun l => passiveParameterChart s₀ (a l)) (fun _ => target s₀) iteration
      (fun rec k => passiveParameterSecondaryChoice s₀ (choice rec k))
      (fun rec k => passiveParameterSecondaryChoice_preserves s₀ (choice rec k)) u (b,x) =
    actualParameterCompleteFirstIncrementFromChoices F hF g label c vf phase tau delta
      backgroundLength probeLength secondaryLength a target iteration choice hc u (s₀,x) := by
  unfold actualParameterCompleteFirstIncrementFromChoices actualParameterCompleteFirstIncrement
  apply congrArg₂ (fun v w : V => v+w)
  · exact passiveParameterBackground_complete_primary s₀ F hF g backgroundLength tau delta target
      label c vf phase probeLength a iteration u b x
  · unfold actualParameterSecondarySourceSum actualSecondaryRefinedNonzeroSum actualSecondaryNonzeroSum
    apply Finset.sum_congr rfl
    intro ν _
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro k _
    dsimp only
    split_ifs with h
    · exact passiveParameterComplete_secondary_piece s₀ F hF g label c vf phase tau delta
        backgroundLength probeLength secondaryLength a target iteration u ((ν,μ),q)
        (choice ⟨((ν,μ),q),h⟩ k) (hc _ _) b x
    · rfl

/-- A genuine physical first map. All parameter dependence is the chosen
global parameter and the actual construction; the reference and primitive
geometry are the passive lifts of the same seed. `F s₀` may already be the
contracted reference used by the original first step. -/
def passiveParameterCompleteFirstMap (u : P → Fin p → ℝ) (z : P × M) : V :=
  F s₀ z.2 + actualParameterCompleteFirstIncrementFromChoices
    (fun _ : P => F s₀) (fun _ => hF s₀) (passiveParameterPrimary s₀ F g)
    label (fun l _ => c l s₀) (fun l _ => vf l s₀)
    (fun l w => phase l (s₀,w.2)) tau delta backgroundLength probeLength secondaryLength
    (fun l => passiveParameterChart s₀ (a l)) (fun _ => target s₀) iteration
    (fun rec k => passiveParameterSecondaryChoice s₀ (choice rec k))
    (fun rec k => passiveParameterSecondaryChoice_preserves s₀ (choice rec k)) (u z.1) z

theorem passiveParameterCompleteFirstMap_eq_seed (u : P → Fin p → ℝ) (b : P) (x : M) :
    passiveParameterCompleteFirstMap s₀ F hF g label c vf phase tau delta
      backgroundLength probeLength secondaryLength a target iteration choice u (b,x) =
    F s₀ x + actualParameterCompleteFirstIncrementFromChoices F hF g label c vf phase tau delta
      backgroundLength probeLength secondaryLength a target iteration choice hc (u b) (s₀,x) := by
  unfold passiveParameterCompleteFirstMap
  rw [passiveParameterComplete_increment s₀ F hF g label c vf phase tau delta
    backgroundLength probeLength secondaryLength a target iteration choice hc (u b) b x]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveParameterComplete_increment
#print axioms GlobalEmbedding.Continuation.passiveParameterCompleteFirstMap_eq_seed
