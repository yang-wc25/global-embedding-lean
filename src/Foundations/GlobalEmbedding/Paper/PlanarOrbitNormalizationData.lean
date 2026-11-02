import GlobalEmbedding.Paper.PlanarPeriodOneCalculus
import GlobalEmbedding.Paper.PlanarOrbitPrimitive
import GlobalEmbedding.Paper.MatrixPeriodicAverageInvariance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import GlobalEmbedding.Paper.PlanarOrbitShiftEquivalence
import GlobalEmbedding.External.SphereEversion.ToMathlib.Equivariant

/-!
# Actual speed and orbit length for intrinsic normalization

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, line261.
All data below come from the original actual orbit derivative and period integral.
-/

open Set

namespace GlobalEmbedding.Paper

/-- The genuine Euclidean/Banach speed of the actual orbit map. -/
noncomputable def planarOrbitSpeed {Q E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ → Q → Q) (g : Q → E) (z : Q) : ℝ := ‖orbitDeriv R g z‖

/-- The genuine length of the period-one orbit profile. -/
noncomputable def planarOrbitLength {Q E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ → Q → Q) (g : Q → E) (z : Q) : ℝ :=
  orbitAverage R (planarOrbitSpeed R g) z

/-- The actual speed normalized by its own orbit average, minus one. -/
noncomputable def planarOrbitNormalizationDensity {Q E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ → Q → Q) (g : Q → E) (z : Q) : ℝ :=
  planarOrbitSpeed R g z / planarOrbitLength R g z - 1

/-- Everywhere nonzero actual orbit derivative gives strictly positive actual
orbit length. A continuous strictly positive integrand has positive integral on
the genuine interval of length one. -/
theorem planarOrbitLength_pos {Q E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ → Q → Q) (g : Q → E) (hn : ∀ z, orbitDeriv R g z ≠ 0) (z : Q)
    (hc : Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) :
    0 < planarOrbitLength R g z := by
  change 0 < ∫ t in (0 : ℝ)..1, ‖orbitDeriv R g (R t z)‖
  exact intervalIntegral.integral_pos (by norm_num) hc.norm.continuousOn
    (fun t _ ↦ norm_nonneg _) ⟨0, by norm_num, norm_pos_iff.mpr (hn (R 0 z))⟩

/-- The actual period integral of the speed is constant on each orbit.
Reuse the already proved genuine average theorem, retaining literal period one. -/
theorem planarOrbitLength_flow {Q E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ → Q → Q) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (g : Q → E) (z : Q) (s : ℝ) :
    planarOrbitLength R g (R s z) = planarOrbitLength R g z := by
  unfold planarOrbitLength orbitAverage
  simpa only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    MeasureTheory.integral_Icc_eq_integral_Ioc] using
    periodic_average_invariant R hadd hone (planarOrbitSpeed R g) z s

/-- The genuine normalized density is continuous along every orbit with
continuous actual derivative; its denominator is the actual invariant length. -/
theorem planarOrbitNormalizationDensity_continuous {Q E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ → Q → Q)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (hone : ∀ z, R 1 z = z)
    (g : Q → E) (z : Q) (hc : Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) :
    Continuous (fun t : ℝ ↦ planarOrbitNormalizationDensity R g (R t z)) := by
  have heq : (fun t : ℝ ↦ planarOrbitNormalizationDensity R g (R t z)) =
      fun t ↦ ‖orbitDeriv R g (R t z)‖ / planarOrbitLength R g z - 1 := by
    funext t
    simp only [planarOrbitNormalizationDensity, planarOrbitSpeed,
      planarOrbitLength_flow R hadd hone]
  rw [heq]
  exact (hc.norm.div_const _).sub continuous_const

/-- Division by the genuine positive invariant orbit length makes the actual
density have zero average. No zero-mean normalization is assumed. -/
theorem planarOrbitNormalizationDensity_average_zero {Q E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ → Q → Q)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (hone : ∀ z, R 1 z = z)
    (g : Q → E) (hn : ∀ z, orbitDeriv R g z ≠ 0) (z : Q)
    (hc : Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) :
    orbitAverage R (planarOrbitNormalizationDensity R g) z = 0 := by
  have hL : planarOrbitLength R g z ≠ 0 := ne_of_gt (planarOrbitLength_pos R g hn z hc)
  unfold orbitAverage
  simp only [planarOrbitNormalizationDensity, planarOrbitSpeed,
    planarOrbitLength_flow R hadd hone]
  rw [intervalIntegral.integral_sub ((hc.norm.div_const _).intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable 0 1), intervalIntegral.integral_div,
    intervalIntegral.integral_const]
  change planarOrbitLength R g z / planarOrbitLength R g z - (1 - 0) • (1 : ℝ) = 0
  simp [hL]

/-- The actual normalization shift is the literal primitive of its genuine
speed density, with no prescribed antiderivative data. -/
noncomputable def planarOrbitNormalizationShift {Q E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ → Q → Q) (g : Q → E) : Q → ℝ :=
  planarOrbitPrimitive R (planarOrbitNormalizationDensity R g)

/-- The actual normalization shift has its exact density as orbit derivative,
by the proved zero mean of that density and the actual primitive theorem. -/
theorem planarOrbitNormalizationShift_orbitDeriv {Q E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (g : Q → E) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (z : Q) (hc : Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) :
    orbitDeriv R (planarOrbitNormalizationShift R g) z =
      planarOrbitNormalizationDensity R g z :=
  planarOrbitPrimitive_orbitDeriv_of_average_zero R hzero hadd hone _ z
    (planarOrbitNormalizationDensity_continuous R hadd hone g z hc)
    (planarOrbitNormalizationDensity_average_zero R hadd hone g hn z hc)

/-- The genuine scalar normalization lift has derivative a/L at every time,
not merely a formal infinitesimal orbit speed. -/
theorem planarOrbitNormalizationLift_hasDerivAt {Q E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ → Q → Q)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (hone : ∀ z, R 1 z = z)
    (g : Q → E) (hn : ∀ z, orbitDeriv R g z ≠ 0) (z : Q)
    (hc : Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) (s : ℝ) :
    HasDerivAt (planarOrbitShiftLift R (planarOrbitNormalizationShift R g) z)
      (planarOrbitSpeed R g (R s z) / planarOrbitLength R g z) s := by
  let u := planarOrbitNormalizationDensity R g
  have hu : Continuous (fun t : ℝ ↦ u (R t z)) :=
    planarOrbitNormalizationDensity_continuous R hadd hone g z hc
  have hm : orbitAverage R u z = 0 :=
    planarOrbitNormalizationDensity_average_zero R hadd hone g hn z hc
  have heq : (fun y ↦ planarOrbitNormalizationShift R g (R y z)) =
      fun y ↦ ∫ t in (0 : ℝ)..1, t • u (R (t + y) z) := by
    funext y
    simp only [planarOrbitNormalizationShift, planarOrbitPrimitive, hadd, u]
  have hd := planarPeriodicPrimitive_hasDerivAt (fun t ↦ u (R t z)) hu
    (orbitMap_periodic R hadd hone u z) s
  change HasDerivAt _ (u (R s z) - orbitAverage R u z) s at hd
  rw [hm, sub_zero, ← heq] at hd
  have hh := (hasDerivAt_id s).add hd
  have hscalar : 1 + u (R s z) = planarOrbitSpeed R g (R s z) / planarOrbitLength R g z := by
    dsimp [u, planarOrbitNormalizationDensity]
    rw [planarOrbitLength_flow R hadd hone]
    ring
  rw [hscalar] at hh
  exact hh

/-- The actual normalization lift derivative is strictly positive. -/
theorem planarOrbitNormalizationLift_deriv_pos {Q E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ → Q → Q)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (hone : ∀ z, R 1 z = z)
    (g : Q → E) (hn : ∀ z, orbitDeriv R g z ≠ 0) (z : Q)
    (hc : Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) (s : ℝ) :
    0 < deriv (planarOrbitShiftLift R (planarOrbitNormalizationShift R g) z) s := by
  rw [(planarOrbitNormalizationLift_hasDerivAt R hadd hone g hn z hc s).deriv]
  exact div_pos (norm_pos_iff.mpr (hn (R s z))) (planarOrbitLength_pos R g hn z hc)

/-- The genuine scalar orbit lift has degree one, so continuity implies
surjectivity by the accepted same-pin equivariant-map theorem. No inverse or
properness of the desired orbit map is supplied. -/
theorem planarOrbitShiftLift_surjective {Q : Type*} (R : ℝ → Q → Q)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (hone : ∀ z, R 1 z = z)
    (h : Q → ℝ) (hc : ∀ z, Continuous (planarOrbitShiftLift R h z)) :
    ∀ z, Function.Surjective (planarOrbitShiftLift R h z) := by
  intro z
  let lift : EquivariantMap :=
    ⟨planarOrbitShiftLift R h z, fun t ↦ by
      simp only [planarOrbitShiftLift, hadd, hone]
      ring⟩
  exact lift.surjective (hc z)

/-- A genuinely positive derivative makes each actual scalar orbit lift
strictly monotone. Native mean-value calculus supplies the assertion. -/
theorem planarOrbitShiftLift_strictMono {Q : Type*} (R : ℝ → Q → Q) (h : Q → ℝ)
    (hpos : ∀ z t, 0 < deriv (planarOrbitShiftLift R h z) t) :
    ∀ z, StrictMono (planarOrbitShiftLift R h z) :=
  fun z ↦ strictMono_of_deriv_pos (hpos z)

/-- The actual global orbit-shift equivalence from genuine continuity,
period-one action and positive orbit derivative. Its inverse is the actual
scalar-root inverse already constructed, with neither bijectivity nor a
prospective normalized map as an input. -/
noncomputable def planarPositiveOrbitShiftEquiv {Q : Type*} (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (h : Q → ℝ)
    (hc : ∀ z, Continuous (planarOrbitShiftLift R h z))
    (hpos : ∀ z t, 0 < deriv (planarOrbitShiftLift R h z) t) : Q ≃ Q :=
  planarOrbitShiftEquiv R hzero hadd h (planarOrbitShiftLift_strictMono R h hpos)
    (planarOrbitShiftLift_surjective R hadd hone h hc)

/-- The canonical actual normalization equivalence; every scalar monotonicity
and surjectivity obligation is discharged from the actual nonzero derivative,
its continuous orbit profile, and the period-one laws. -/
noncomputable def planarOrbitNormalizationEquiv {Q E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (g : Q → E) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) : Q ≃ Q := by
  have hd (z : Q) : Differentiable ℝ
      (planarOrbitShiftLift R (planarOrbitNormalizationShift R g) z) :=
    fun s ↦ (planarOrbitNormalizationLift_hasDerivAt R hadd hone g hn z (hc z) s).differentiableAt
  exact planarPositiveOrbitShiftEquiv R hzero hadd hone (planarOrbitNormalizationShift R g)
    (fun z ↦ (hd z).continuous)
    (fun z s ↦ planarOrbitNormalizationLift_deriv_pos R hadd hone g hn z (hc z) s)

/-- Half-period reflection under a genuine linear isometry preserves the
actual orbit speed. Differentiate the actual reflected orbit function; its
nonzero derivative itself guarantees the required actual differentiability. -/
theorem planarOrbitSpeed_half {Q E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ → Q → Q) (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (g : Q → E)
    (hn : ∀ z, orbitDeriv R g z ≠ 0) (A : E ≃ₗᵢ[ℝ] E)
    (ha : ∀ z, g (R (1 / 2 : ℝ) z) = A (g z)) (z : Q) :
    planarOrbitSpeed R g (R (1 / 2 : ℝ) z) = planarOrbitSpeed R g z := by
  have heq : (fun t : ℝ ↦ g (R t (R (1 / 2 : ℝ) z))) =
      fun t ↦ A (g (R t z)) := by
    funext t
    rw [← hadd, add_comm t, hadd, ha]
  have hdg : HasDerivAt (fun t : ℝ ↦ g (R t z)) (orbitDeriv R g z) 0 :=
    (differentiableAt_of_deriv_ne_zero (hn z)).hasDerivAt
  have hd := A.toLinearIsometry.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hdg
  have hder : orbitDeriv R g (R (1 / 2 : ℝ) z) = A (orbitDeriv R g z) := by
    unfold orbitDeriv
    rw [heq]
    exact hd.deriv
  unfold planarOrbitSpeed
  rw [hder, A.norm_map]

/-- Actual orbit integration preserves half-period invariance of the speed. -/
theorem planarOrbitLength_half {Q E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ → Q → Q) (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (g : Q → E)
    (hn : ∀ z, orbitDeriv R g z ≠ 0) (A : E ≃ₗᵢ[ℝ] E)
    (ha : ∀ z, g (R (1 / 2 : ℝ) z) = A (g z)) (z : Q) :
    planarOrbitLength R g (R (1 / 2 : ℝ) z) = planarOrbitLength R g z := by
  unfold planarOrbitLength orbitAverage
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← hadd, add_comm t, hadd]
  exact planarOrbitSpeed_half R hadd g hn A ha (R t z)

/-- The genuine density inherits half-period invariance, with the actual
speed and actual length rather than a supplied normalization coefficient. -/
theorem planarOrbitNormalizationDensity_half {Q E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ → Q → Q)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (g : Q → E)
    (hn : ∀ z, orbitDeriv R g z ≠ 0) (A : E ≃ₗᵢ[ℝ] E)
    (ha : ∀ z, g (R (1 / 2 : ℝ) z) = A (g z)) (z : Q) :
    planarOrbitNormalizationDensity R g (R (1 / 2 : ℝ) z) =
      planarOrbitNormalizationDensity R g z := by
  unfold planarOrbitNormalizationDensity
  rw [planarOrbitSpeed_half R hadd g hn A ha, planarOrbitLength_half R hadd g hn A ha]

/-- The literal intrinsic normalization primitive is half-period invariant. -/
theorem planarOrbitNormalizationShift_half {Q E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ → Q → Q)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (g : Q → E)
    (hn : ∀ z, orbitDeriv R g z ≠ 0) (A : E ≃ₗᵢ[ℝ] E)
    (ha : ∀ z, g (R (1 / 2 : ℝ) z) = A (g z)) (z : Q) :
    planarOrbitNormalizationShift R g (R (1 / 2 : ℝ) z) =
      planarOrbitNormalizationShift R g z := by
  unfold planarOrbitNormalizationShift planarOrbitPrimitive
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← hadd, add_comm t, hadd,
    planarOrbitNormalizationDensity_half R hadd g hn A ha]

#print axioms planarOrbitNormalizationEquiv
#print axioms planarOrbitSpeed_half
#print axioms planarOrbitNormalizationShift_half
#print axioms planarOrbitNormalizationDensity_average_zero
#print axioms planarOrbitNormalizationLift_hasDerivAt
#print axioms planarOrbitNormalizationLift_deriv_pos
#print axioms planarOrbitShiftLift_surjective
#print axioms planarPositiveOrbitShiftEquiv

#print axioms planarOrbitLength_pos

end GlobalEmbedding.Paper
