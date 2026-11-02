import NormalPolar.ActualProbeSecondaryParameterForcing
import Probes.Round3ParameterSecondaryLocality

/-! Exact diagonal identity for a single genuine joint secondary family.

The whole joint primary fields are inserted before forming their spatial
quadratic tensor. At a fixed physical parameter their complete spatial slices
agree with the fixed-external-parameter construction. The two inverse tensor
Jacobians and the full finite inhomogeneous solver preserve this identity.
No secondary witness is selected pointwise and no choice is differentiated.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {P M U Label : Type*} {m N : ℕ}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => P × D
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

theorem jointSecondary_quadratic_diagonal
    (phase : Label → P × M → ℝ) (R Q : U → Label → P × M → V)
    (u : P → U) (tau : ℝ) (host : OpenPartialHomeomorph M D)
    (rec : (Label × Label) × Fin 4) (z : X) :
    actualParameterPrimaryQuadratic phase
      (fun l y => R (u y.1) l y) (fun l y => Q (u y.1) l y) tau host rec z =
      actualParameterPrimaryQuadratic phase (R (u z.1)) (Q (u z.1)) tau host rec z := rfl

theorem jointSecondary_inverse_forcing_diagonal
    (choice : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves choice.chart)
    (H : U → X → Tensor) (u : P → U) (z : X) (hz : z ∈ choice.chart.target) :
    round3ParameterInverseForcing (round3ParameterSecondaryTransition choice)
      (choice.cutoff ∘ ((OpenPartialHomeomorph.refl P).prod choice.host).symm)
      (fun y => H (u y.1) y) z =
    round3ParameterInverseForcing (round3ParameterSecondaryTransition choice)
      (choice.cutoff ∘ ((OpenPartialHomeomorph.refl P).prod choice.host).symm)
      (H (u z.1)) z := by
  have hp : ((round3ParameterSecondaryTransition choice).symm z).1 = z.1 :=
    round3ParameterChartPreserves_inverse choice.chart hc z hz
  unfold round3ParameterInverseForcing round3ParameterInverseForcingTensor
  dsimp only
  rw [hp]

def jointSecondaryDiagonalPrimarySource
    (phase : Label → P × M → ℝ) (R Q : U → Label → P × M → V)
    (u : P → U) (tau : ℝ) (rec : (Label × Label) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves choice.chart) : ActualProbeSecondaryParameterSource P M m :=
  actualParameterSecondarySourceOfPrimary phase
    (fun l y => R (u y.1) l y) (fun l y => Q (u y.1) l y) tau rec choice hc

theorem jointSecondary_diagonal_forcing
    (phase : Label → P × M → ℝ) (R Q : U → Label → P × M → V)
    (u : P → U) (tau : ℝ) (rec : (Label × Label) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves choice.chart) (z : X) (hz : z ∈ choice.chart.target) :
    let joint := jointSecondaryDiagonalPrimarySource phase R Q u tau rec choice hc
    let fixed := actualParameterSecondarySourceOfPrimary phase (R (u z.1)) (Q (u z.1)) tau rec choice hc
    joint.forcingR z = fixed.forcingR z ∧ joint.forcingI z = fixed.forcingI z := by
  intro joint fixed
  constructor
  · exact jointSecondary_inverse_forcing_diagonal choice hc
      (fun v y => actualRealTensorAssembly (actualParameterPrimaryQuadratic phase (R v) (Q v)
        tau choice.host rec y)) u z hz
  · exact jointSecondary_inverse_forcing_diagonal choice hc
      (fun v y => actualImaginaryTensorAssembly (actualParameterPrimaryQuadratic phase (R v) (Q v)
        tau choice.host rec y)) u z hz

section Waves

theorem jointSecondary_diagonal_complete_wave
    (F : P → M → V) (hF : ∀ b, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F b))
    (phase : Label → P × M → ℝ) (R Q : U → Label → P × M → V)
    (u : P → U) (tau : ℝ) (rec : (Label × Label) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves choice.chart)
    (tau' : ℝ) (length : ℕ) (b : P) (x : M) :
    (jointSecondaryDiagonalPrimarySource phase R Q u tau rec choice hc).wave F hF tau' length (b,x) =
    (actualParameterSecondarySourceOfPrimary phase (R (u b)) (Q (u b)) tau rec choice hc).wave
      F hF tau' length (b,x) := by
  classical
  let joint := jointSecondaryDiagonalPrimarySource phase R Q u tau rec choice hc
  let fixed := actualParameterSecondarySourceOfPrimary phase (R (u b)) (Q (u b)) tau rec choice hc
  let O : Set D := {y | (b,y) ∈ choice.chart.target}
  have hO : IsOpen O := choice.chart.open_target.preimage (continuous_const.prodMk continuous_id)
  have hr : EqOn (fun y => joint.forcingR (b,y)) (fun y => fixed.forcingR (b,y)) O :=
    fun y hy => (jointSecondary_diagonal_forcing phase R Q u tau rec choice hc (b,y) hy).1
  have hi : EqOn (fun y => joint.forcingI (b,y)) (fun y => fixed.forcingI (b,y)) O :=
    fun y hy => (jointSecondary_diagonal_forcing phase R Q u tau rec choice hc (b,y) hy).2
  by_cases hx : (b,x) ∈ choice.chart.source
  · have hp : choice.chart (b,x) = (b,(choice.chart (b,x)).2) := Prod.ext (hc _ hx) rfl
    have ht : (choice.chart (b,x)).2 ∈ O := by
      change (b,(choice.chart (b,x)).2) ∈ choice.chart.target
      rw [← hp]
      exact choice.chart.map_source hx
    have hreal := round3ParameterSecondary_realChannel_eqOn F hF choice.c
      joint.forcingR joint.forcingI fixed.forcingR fixed.forcingI b O hr hi hO tau' length ht
    have himag := round3ParameterSecondary_imagChannel_eqOn F hF choice.c
      joint.forcingR joint.forcingI fixed.forcingR fixed.forcingI b O hr hi hO tau' length ht
    dsimp only at hreal himag
    change round3ParameterSupportedWave F hF choice.c joint.forcingR joint.forcingI choice.chart
      joint.phase tau' length (b,x) =
      round3ParameterSupportedWave F hF choice.c fixed.forcingR fixed.forcingI choice.chart
        fixed.phase tau' length (b,x)
    unfold round3ParameterSupportedWave
    rw [if_pos hx,if_pos hx,if_pos hx,if_pos hx,hp,hreal,himag]
    rfl
  · change round3ParameterSupportedWave F hF choice.c joint.forcingR joint.forcingI choice.chart
      joint.phase tau' length (b,x) =
      round3ParameterSupportedWave F hF choice.c fixed.forcingR fixed.forcingI choice.chart
        fixed.phase tau' length (b,x)
    simp only [round3ParameterSupportedWave,if_neg hx,smul_zero,sub_self]

theorem jointSecondary_diagonal_complete_sum
    {Sub : Type*} [Fintype Sub] [Fintype Label] [DecidableEq Label]
    (F : P → M → V) (hF : ∀ b, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F b))
    (phase : Label → P × M → ℝ) (R Q : U → Label → P × M → V)
    (u : P → U) (tau : ℝ)
    (choice : ActualSecondarySignedRecord Label → Sub → Round3ParameterSecondaryChoice P M m)
    (hc : ∀ rec k, Round3ParameterChartPreserves (choice rec k).chart)
    (tau' : ℝ) (length : ℕ) (b : P) (x : M) :
    actualParameterSecondarySourceSum F hF
      (fun rec k => jointSecondaryDiagonalPrimarySource phase R Q u tau rec.val (choice rec k) (hc rec k))
      tau' length (b,x) =
    actualParameterSecondarySourceSum F hF
      (fun rec k => actualParameterSecondarySourceOfPrimary phase (R (u b)) (Q (u b)) tau rec.val
        (choice rec k) (hc rec k)) tau' length (b,x) := by
  unfold actualParameterSecondarySourceSum actualSecondaryRefinedNonzeroSum actualSecondaryNonzeroSum
  apply Finset.sum_congr rfl
  intro nu _
  apply Finset.sum_congr rfl
  intro mu _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  split_ifs with h
  · exact jointSecondary_diagonal_complete_wave F hF phase R Q u tau ((nu,mu),q)
      (choice ⟨((nu,mu),q),h⟩ k) (hc _ _) tau' length b x
  · rfl

end Waves
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_diagonal_complete_wave
#print axioms GlobalEmbedding.Continuation.jointSecondary_diagonal_complete_sum
