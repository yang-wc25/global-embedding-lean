import Probes.ActualFullProbeFirstStep

/-!
# Joint smoothness of the actual finite homogeneous first step

The original solver family's local finite source linearity supplies genuine
joint parameter/spatial smoothness on the original open chart. No global
extension of the phase, amplitude or geometric fields is needed.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Set Manifold
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Offline

section JointFinite
variable {X Y ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype ι]

/-- The actual finite source span is jointly smooth in parameters and space. -/
theorem finiteProbeSource_joint_contDiffOn (g : ι → X → Y) (O : Set X)
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) O) :
    ContDiffOn ℝ ∞ (fun z : (ι → ℝ) × X ↦ finiteProbeSource g z.1 z.2) (univ ×ˢ O) := by
  apply ContDiffOn.sum
  intro i _
  have hp : ContDiffOn ℝ ∞ (fun z : (ι → ℝ) × X ↦ z.1 i) (univ ×ˢ O) :=
    ((ContinuousLinearMap.proj i) : (ι → ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn contDiffOn_fst
  have hx : ContDiffOn ℝ ∞ (fun z : (ι → ℝ) × X ↦ g i z.2) (univ ×ˢ O) :=
    (hg i).comp contDiffOn_snd (fun _ hz ↦ hz.2)
  exact hp.smul hx
end JointFinite

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ

-- Native nested operator structures, fixed to avoid redundant typeclass search.
private noncomputable local instance fullProbeBilinearSemi :
    SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance fullProbeBilinearNormed :
    NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance fullProbeBilinearNormedSpace :
    NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace


/-- The complete SAME finite free-plus-reconstructed probe block is jointly
smooth on the original parameter-space times spatial chart. -/
theorem actualFiniteProbeWithReconstruction_joint_contDiffOn
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ) (amplitude : Fin r → D → V)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (order : ℕ) (k : Fin r → Fin p → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hphase : ∀ l, ContDiffOn ℝ ∞ (phase l) O)
    (hamplitude : ∀ l, ContDiffOn ℝ ∞ (amplitude l) O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hk : ∀ l q, ContDiffOn ℝ ∞ (k l q) O) :
    ContDiffOn ℝ ∞ (fun z : (Fin p → ℝ) × D ↦
      actualFiniteProbeWithReconstruction label δ τ weight phase amplitude F hF c order k z.1 z.2)
      (univ ×ˢ O) := by
  classical
  have hcos (l : Fin r) : ContDiffOn ℝ ∞
      (actualProbeCosColumn δ τ (weight l) (phase l) (amplitude l)) O :=
    (((hphase l).const_smul (weight l / τ)).cos.smul (hamplitude l)).const_smul (-(δ * τ / weight l ^ 2))
  have hsin (l : Fin r) : ContDiffOn ℝ ∞
      (actualProbeSinColumn δ τ (weight l) (phase l) (amplitude l)) O :=
    (((hphase l).const_smul (weight l / τ)).sin.smul (hamplitude l)).const_smul (-(δ * τ / weight l ^ 2))
  have hfree : ContDiffOn ℝ ∞ (fun z : (Fin p → ℝ) × D ↦
      actualFiniteProbeDisplacement label δ τ weight phase amplitude z.1 z.2) (univ ×ˢ O) := by
    have heq : (fun z : (Fin p → ℝ) × D ↦
        actualFiniteProbeDisplacement label δ τ weight phase amplitude z.1 z.2) = fun z ↦
        ∑ l, (z.1 (label (l, false)) • actualProbeCosColumn δ τ (weight l) (phase l) (amplitude l) z.2 +
          z.1 (label (l, true)) • actualProbeSinColumn δ τ (weight l) (phase l) (amplitude l) z.2) := by
      funext z
      exact actualFiniteProbeDisplacement_eq_sum label δ τ weight phase amplitude z.1 z.2
    rw [heq]
    apply ContDiffOn.sum
    intro l _
    have hpc : ContDiffOn ℝ ∞ (fun z : (Fin p → ℝ) × D ↦ z.1 (label (l, false))) (univ ×ˢ O) :=
      ((ContinuousLinearMap.proj (label (l, false))) : (Fin p → ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn contDiffOn_fst
    have hps : ContDiffOn ℝ ∞ (fun z : (Fin p → ℝ) × D ↦ z.1 (label (l, true))) (univ ×ˢ O) :=
      ((ContinuousLinearMap.proj (label (l, true))) : (Fin p → ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn contDiffOn_fst
    have hxc : ContDiffOn ℝ ∞ (fun z : (Fin p → ℝ) × D ↦
        actualProbeCosColumn δ τ (weight l) (phase l) (amplitude l) z.2) (univ ×ˢ O) :=
      (hcos l).comp contDiffOn_snd (fun _ hz ↦ hz.2)
    have hxs : ContDiffOn ℝ ∞ (fun z : (Fin p → ℝ) × D ↦
        actualProbeSinColumn δ τ (weight l) (phase l) (amplitude l) z.2) (univ ×ˢ O) :=
      (hsin l).comp contDiffOn_snd (fun _ hz ↦ hz.2)
    exact (hpc.smul hxc).add (hps.smul hxs)
  have hrec (l : Fin r) : ContDiffOn ℝ ∞ (fun z : (Fin p → ℝ) × D ↦
      actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order
        (finiteProbeSource (k l) z.1) z.2) (univ ×ˢ O) := by
    have hs := finiteProbeSource_joint_contDiffOn
      (fun q ↦ actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order (k l q)) O
      (fun q ↦ actualRealHomogeneousProbe_contDiffOn _ F hF c τ order (k l q)
        O hO ((hphase l).const_smul (weight l)) hA hB hG hJ hT0 (hk l q))
    apply hs.congr
    intro z hz
    exact actualRealHomogeneousProbe_finite_source _ F hF c τ order (k l) O hO hA hB (hk l)
      z.2 hz.2 z.1
  exact hfree.add (ContDiffOn.sum (fun l _ ↦ hrec l))

#print axioms actualFiniteProbeWithReconstruction_joint_contDiffOn
end GlobalEmbedding.Offline
