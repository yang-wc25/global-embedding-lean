import NormalPolar.ParameterDisplacementCombinedParameterNaturality
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
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P]
  {m N p r : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem jointMixed_combined_mean_eq
    (F : P → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p) (c : Fin r → P → D → M)
    (vf : (l : Fin r) → (b : P) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (P × M) (P × D))
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Fin p → ℝ) (b : P) (x : M)
    (hamp : ∀ l ch, MDifferentiableAt I 𝓘(ℝ,V)
      (fun y => round3ParameterPrimaryAmplitude F hF g input backgroundLength tau ch l (b,y)) x) :
    actualParameterProbeCombinedMean F hF g label c vf phase tau delta backgroundLength
      probeLength a input u b x =
      delta^2 • round3ParameterPrimaryMean F hF g input backgroundLength tau b x +
        actualParameterPrescribedNativeMean label F hF c vf phase tau probeLength a u b x := by
  have hcoef (imag : Bool) (l : Λ) :
      round4PrescribedNativeCoefficient (I := I) imag (g.phase l) tau
        (fun z => delta • round3ParameterPrimaryAmplitude F hF g input backgroundLength tau true l z)
        (fun z => delta • round3ParameterPrimaryAmplitude F hF g input backgroundLength tau false l z) (b,x) =
      delta • round3ParameterPrimaryCoefficient F hF g input backgroundLength tau (!imag) l (b,x) := by
    rw [round4Parameter_native_coefficient_smul imag (g.phase l) tau delta _ _ (b,x)
      (hamp l true) (hamp l false)]
    congr 1
    cases imag <;> rfl
  simp only [actualParameterProbeCombinedMean,actualParameterProbeCombinedAmplitude,
    Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Bool.not_false,Bool.not_true,
    smul_add,hcoef]
  change (1/2 : ℝ) • (∑ l : Λ, _) +
    actualParameterPrescribedNativeMean label F hF c vf phase tau probeLength a u b x = _
  congr 1
  ext v w
  simp only [round3ParameterPrimaryMean,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.add_apply,LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,
    innerₗ_apply_apply,smul_apply,real_inner_smul_left,real_inner_smul_right,smul_eq_mul,
    Finset.mul_sum,mul_add]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Actual primitive smoothness on one genuine parameter chart supplies the
spatial differentiability of the original global amplitude at that point. -/
theorem jointMixed_primary_spatial_mdiff_from_raw
    {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    (F : P → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
    (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
    (B : OpenPartialHomeomorph P Ep)
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (P × M)) (primary : Λ → Set (P × M))
    (raw : ParameterRound2GlobalMeanPrimitives
      (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      ((round3ParameterPrimaryPullback F g B).toNative (fun t => F (B.symm t)))
      (fun t => input (B.symm t)) (round3ParameterNativeDomain B W)
      (fun l => round3ParameterNativeDomain B (primary l)))
    (length : ℕ) (tau : ℝ) (b : P) (hb : b ∈ B.source) (x : M) (hx : (b,x) ∈ W) :
    ∀ l ch, MDifferentiableAt I 𝓘(ℝ,V)
      (fun y => round3ParameterPrimaryAmplitude F hF g input length tau ch l (b,y)) x := by
  intro l ch
  let Fbar := fun t => F (B.symm t)
  let hFbar := fun t => hF (B.symm t)
  let gbar := (round3ParameterPrimaryPullback F g B).toNative Fbar
  let native := incrementsGlobalPrimaryAmplitude Fbar hFbar gbar
    (fun t => input (B.symm t)) length tau ch l
  have hmem : (B b,x) ∈ round3ParameterNativeDomain B W := by
    exact ⟨B.map_source hb,by simpa only [B.left_inv hb] using hx⟩
  have hr := (actualRepairModelFirstDefect_background_amplitude_regular Fbar hFbar gbar
    (fun t => input (B.symm t)) (round3ParameterNativeDomain B W)
    (fun l => round3ParameterNativeDomain B (primary l)) raw length tau ch l).1
  have hs : MDifferentiableAt I 𝓘(ℝ,V) (fun y : M => native (B b,y)) x :=
    ((hr.contMDiffAt (raw.hW.mem_nhds hmem)).comp x
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt).mdifferentiableAt (by simp)
  have he : (fun y : M => native (B b,y)) =
      fun y => round3ParameterPrimaryAmplitude F hF g input length tau ch l (b,y) := by
    funext y
    change round3ParameterPrimaryAmplitude (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t))
      length tau ch l (B b,y) = _
    have hp := round3ParameterPrimary_pullback_amplitude F hF g B hg input length tau
      ch l (B b) (B.map_source hb) y
    simpa only [B.left_inv hb] using hp
  rwa [he] at hs

/-- The mean decomposition is a conclusion of the same raw background input.
The value u b is substituted only after the whole-field construction. -/
theorem jointMixed_combined_mean_from_raw
    {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    (F : P → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
    (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
    (label : (Fin r × Bool) ↪ Fin p) (c : Fin r → P → D → M)
    (vf : (l : Fin r) → (b : P) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (P × M) (P × D))
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : P → Fin p → ℝ) (W : Set (P × M)) (primary : Λ → Set (P × M))
    (B : OpenPartialHomeomorph P Ep)
    (raw : ParameterRound2GlobalMeanPrimitives
      (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      ((round3ParameterPrimaryPullback F g B).toNative (fun t => F (B.symm t)))
      (fun t => input (B.symm t)) (round3ParameterNativeDomain B W)
      (fun l => round3ParameterNativeDomain B (primary l)))
    (b : P) (hb : b ∈ B.source) (x : M) (hx : (b,x) ∈ W) :
    actualParameterProbeCombinedMean F hF g label c vf phase tau delta backgroundLength
      probeLength a input (u b) b x =
      delta^2 • round3ParameterPrimaryMean F hF g input backgroundLength tau b x +
        actualParameterPrescribedNativeMean label F hF c vf phase tau probeLength a (u b) b x :=
  jointMixed_combined_mean_eq F hF g label c vf phase tau delta backgroundLength probeLength
    a input (u b) b x
    (jointMixed_primary_spatial_mdiff_from_raw F hF g hg B input W primary raw
      backgroundLength tau b hb x hx)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointMixed_combined_mean_eq
#print axioms GlobalEmbedding.Continuation.jointMixed_primary_spatial_mdiff_from_raw
#print axioms GlobalEmbedding.Continuation.jointMixed_combined_mean_from_raw
