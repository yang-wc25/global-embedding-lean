import NormalPolar.ActualProbeInitialSupplyGroupedAmplitude
import NormalPolar.JointSecondaryGroupedEvaluation
import NormalPolar.JointMixedCombinedMean
import NormalPolar.ParameterDisplacementPrescribedMeanNaturality
import NormalPolar.ActualRepairModelFirstDefectAmplitude
import Probes.Round3ParameterRawAtlasData

/-!
# The physical combined mean splits on the original parameter space

The background is the same whole tensor input as in the forced iteration.
Only source differentiation occurs in the coefficient identity. Its required
regularity is produced from an actual native primitive record and pulled back
to the physical parameter point. No parameter Euclidean-space assumption,
completed mean estimate, or fixed-parameter existence choice is introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {M P : Type*} {m N p r : ℕ} [TopologicalSpace P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

attribute [local irreducible] OpenPartialHomeomorph.symm

private theorem actualProbeInitialSupply_grouped_gram_symmetric (x : M)
    (C : Bool → (Λ ⊕ Fin r) → TangentSpace IM x →L[ℝ] V) :
    ((1/2 : ℝ) • ∑ l,
      (LinearMap.BilinForm.comp (innerₗ V) (C false l).toLinearMap (C false l).toLinearMap +
      LinearMap.BilinForm.comp (innerₗ V) (C true l).toLinearMap (C true l).toLinearMap)).IsSymm := by
  constructor
  intro v w
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.add_apply,
    LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,innerₗ_apply_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  exact congrArg₂ (fun a b : ℝ => a+b) (real_inner_comm _ _) (real_inner_comm _ _)

theorem actualProbeInitialGroupedMean_isSymm
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p) (c : (l : Fin r) → Pieces l → P → D → M)
    (vf : (l : Fin r) → (s : Pieces l) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × D))
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : P → Fin p → ℝ) (b : P) (x : M)
 :
    (actualProbeInitialGroupedMean F hF g label c vf phase tau delta backgroundLength
      probeLength a input u b x).IsSymm := by
  exact actualProbeInitialSupply_grouped_gram_symmetric x
    (fun ch l => round4PrescribedNativeCoefficient (I := IM) ch (Sum.elim g.phase phase l) tau
      (actualProbeInitialGroupedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false l)
      (actualProbeInitialGroupedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true l) (b,x))

theorem actualProbeInitialSupply_grouped_mean_eq
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p) (c : (l : Fin r) → Pieces l → P → D → M)
    (vf : (l : Fin r) → (s : Pieces l) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × D))
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : P → Fin p → ℝ) (b : P) (x : M)
    (hamp : ∀ l ch, MDifferentiableAt IM 𝓘(ℝ,V)
      (fun y => round3ParameterPrimaryAmplitude F hF g input backgroundLength tau ch l (b,y)) x) :
    actualProbeInitialGroupedMean F hF g label c vf phase tau delta backgroundLength
      probeLength a input u b x =
      delta^2 • round3ParameterPrimaryMean F hF g input backgroundLength tau b x +
        jointGroupedParameterPrescribedMean label F hF c vf phase tau probeLength a (u b) b x := by
  have hcoef (imag : Bool) (l : Λ) :
      round4PrescribedNativeCoefficient (I := IM) imag (g.phase l) tau
        (fun z => delta • round3ParameterPrimaryAmplitude F hF g input backgroundLength tau true l z)
        (fun z => delta • round3ParameterPrimaryAmplitude F hF g input backgroundLength tau false l z) (b,x) =
      delta • round3ParameterPrimaryCoefficient F hF g input backgroundLength tau (!imag) l (b,x) := by
    rw [round4Parameter_native_coefficient_smul imag (g.phase l) tau delta _ _ (b,x)
      (hamp l true) (hamp l false)]
    congr 1
    cases imag <;> rfl
  have hprobe (ch : Bool) (l : Fin r) :
      round4PrescribedNativeCoefficient (I := IM) ch (phase l) tau
        (fun z => jointGroupedParameterPrescribedAmplitude label F hF c vf tau probeLength a false (u z.1) l z)
        (fun z => jointGroupedParameterPrescribedAmplitude label F hF c vf tau probeLength a true (u z.1) l z) (b,x) =
      round4PrescribedNativeCoefficient (I := IM) ch (phase l) tau
        (jointGroupedParameterPrescribedAmplitude label F hF c vf tau probeLength a false (u b) l)
        (jointGroupedParameterPrescribedAmplitude label F hF c vf tau probeLength a true (u b) l) (b,x) :=
    jointGrouped_native_coefficient_diagonal ch (phase l) tau
      (fun v => jointGroupedParameterPrescribedAmplitude label F hF c vf tau probeLength a false v l)
      (fun v => jointGroupedParameterPrescribedAmplitude label F hF c vf tau probeLength a true v l) u b x
  simp only [actualProbeInitialGroupedMean,actualProbeInitialGroupedAmplitude,
    Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Bool.not_false,Bool.not_true,
    smul_add,hcoef,hprobe]
  change (1/2 : ℝ) • (∑ l : Λ, _) +
    jointGroupedParameterPrescribedMean label F hF c vf phase tau probeLength a (u b) b x = _
  congr 1
  ext v w
  simp only [round3ParameterPrimaryMean,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.add_apply,LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,
    innerₗ_apply_apply,smul_apply,real_inner_smul_left,real_inner_smul_right,smul_eq_mul,
    Finset.mul_sum,mul_add]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The mean decomposition is a conclusion of the same raw background input.
The value u b is substituted only after the whole-field construction. -/
theorem actualProbeInitialSupply_grouped_mean_from_raw
    {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
    (label : (Fin r × Bool) ↪ Fin p) (c : (l : Fin r) → Pieces l → P → D → M)
    (vf : (l : Fin r) → (s : Pieces l) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × D))
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : P → Fin p → ℝ) (W : Set (P × M)) (primary : Λ → Set (P × M))
    (B : OpenPartialHomeomorph P Ep)
    (raw : ParameterRound2GlobalMeanPrimitives
      (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      ((round3ParameterPrimaryPullback F g B).toNative (fun t => F (B.symm t)))
      (fun t => input (B.symm t)) (round3ParameterNativeDomain B W)
      (fun l => round3ParameterNativeDomain B (primary l)))
    (b : P) (hb : b ∈ B.source) (x : M) (hx : (b,x) ∈ W) :
    actualProbeInitialGroupedMean F hF g label c vf phase tau delta backgroundLength
      probeLength a input u b x =
      delta^2 • round3ParameterPrimaryMean F hF g input backgroundLength tau b x +
        jointGroupedParameterPrescribedMean label F hF c vf phase tau probeLength a (u b) b x :=
  actualProbeInitialSupply_grouped_mean_eq F hF g label c vf phase tau delta backgroundLength probeLength
    a input u b x
    (jointMixed_primary_spatial_mdiff_from_raw F hF g hg B input W primary raw
      backgroundLength tau b hb x hx)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_grouped_mean_eq
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_grouped_mean_from_raw

#print axioms GlobalEmbedding.Continuation.actualProbeInitialGroupedMean_isSymm
