import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Complex.Basic

/-!
# Complex analytic germs are determined by their real-coordinate restrictions

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Actual local extensions must agree before they can be glued.
-/

open Set Filter
open scoped Topology

namespace GlobalEmbedding.Paper

/-- Two complex analytic germs agreeing at all nearby real-coordinate points agree on an
actual complex neighborhood.

Source: Proposition `prop:collar`, proof lines 530–534, uniqueness for local complex
extensions. Subtract the functions. Every real jet of the restriction vanishes. The local
linear chain rule and restriction of scalars show that every complex jet vanishes on all
real standard-basis tuples. Full complex multilinearity and the finite-basis expansion then
force the complex jet itself to vanish. The genuine normalized-derivative Taylor sum is
therefore zero on a complex neighborhood. No real subset is treated as complex open. -/
theorem collar_complex_real_germ_uniqueness
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    {m : ℕ} (f h : (Fin m → ℂ) → F) (x : Fin m → ℝ)
    (hf : AnalyticAt ℂ f (fun j ↦ (x j : ℂ)))
    (hh : AnalyticAt ℂ h (fun j ↦ (x j : ℂ)))
    (heq : (fun y : Fin m → ℝ ↦ f (fun j ↦ (y j : ℂ))) =ᶠ[𝓝 x]
      (fun y : Fin m → ℝ ↦ h (fun j ↦ (y j : ℂ)))) :
    f =ᶠ[𝓝 (fun j ↦ (x j : ℂ))] h := by
  classical
  let ι : (Fin m → ℝ) →L[ℝ] (Fin m → ℂ) :=
    ContinuousLinearMap.pi (fun j ↦ Complex.ofRealCLM.comp (ContinuousLinearMap.proj j))
  have hι (y : Fin m → ℝ) (j : Fin m) : ι y j = (y j : ℂ) := rfl
  have hιsingle (j : Fin m) : ι (Pi.single j 1) = Pi.single j 1 := by
    ext l
    by_cases hl : l = j <;> simp [hι, hl]
  let g : (Fin m → ℂ) → F := fun z ↦ f z - h z
  have hg : AnalyticAt ℂ g (ι x) := hf.sub hh
  have hz : (g ∘ ι) =ᶠ[𝓝 x] (0 : (Fin m → ℝ) → F) := by
    filter_upwards [heq] with y hy
    exact sub_eq_zero.mpr hy
  have hjets (n : ℕ) : iteratedFDeriv ℂ n g (ι x) = 0 := by
    have hc : ContDiffAt ℂ n g (ι x) := hg.contDiffAt
    have hr : ContDiffAt ℝ n g (ι x) := hg.restrictScalars.contDiffAt
    obtain ⟨U, hU, hxU, hgU⟩ := hr.contDiffOn' le_rfl (by simp)
    have hgU' : ContDiffOn ℝ n g U := by simpa using hgU
    have hV : IsOpen (ι ⁻¹' U) := hU.preimage ι.continuous
    have hcomp : iteratedFDeriv ℝ n (g ∘ ι) x =
        (iteratedFDeriv ℝ n g (ι x)).compContinuousLinearMap (fun _ : Fin n ↦ ι) := by
      rw [← iteratedFDerivWithin_of_isOpen n hV hxU,
        ← iteratedFDerivWithin_of_isOpen n hU hxU]
      exact ι.iteratedFDerivWithin_comp_right hgU' hU.uniqueDiffOn hV.uniqueDiffOn hxU le_rfl
    have hzero : iteratedFDeriv ℝ n (g ∘ ι) x = 0 := by
      have he := (hz.iteratedFDeriv ℝ n).eq_of_nhds
      simpa using he
    rw [← hc.restrictScalars_iteratedFDeriv, Function.comp_apply] at hcomp
    have hbase (σ : Fin n → Fin m) :
        iteratedFDeriv ℂ n g (ι x) (fun i ↦ Pi.single (σ i) (1 : ℂ)) = 0 := by
      have he := congrArg (fun q : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Fin m → ℝ) F ↦
        q (fun i ↦ Pi.single (σ i) 1)) (hcomp.symm.trans hzero)
      change iteratedFDeriv ℂ n g (ι x) (fun i ↦ ι (Pi.single (σ i) 1)) = 0 at he
      simpa only [hιsingle] using he
    apply ContinuousMultilinearMap.ext
    intro v
    have hv : (fun i ↦ ∑ j : Fin m, v i j • (Pi.single j 1 : Fin m → ℂ)) = v := by
      funext i j
      simp [Finset.sum_apply, Pi.single_apply]
    change iteratedFDeriv ℂ n g (ι x) v = 0
    rw [← hv, ContinuousMultilinearMap.map_sum]
    simp only [ContinuousMultilinearMap.map_smul_univ, hbase, smul_zero, Finset.sum_const_zero]
  obtain ⟨p, r, hp⟩ := hg
  have hball : Metric.eball (ι x) r ∈ 𝓝 (ι x) :=
    Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self hp.r_pos)
  filter_upwards [hball] with z hzball
  have hz' : z - ι x ∈ Metric.eball (0 : Fin m → ℂ) r := by
    simpa only [Metric.mem_eball, edist_dist, dist_eq_norm, sub_zero] using hzball
  have hs := hp.hasSum_iteratedFDeriv hz'
  simp only [hjets, zero_apply, smul_zero] at hs
  have he : g z = 0 := by
    simpa only [add_sub_cancel] using hs.unique hasSum_zero
  exact sub_eq_zero.mp he

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_complex_real_germ_uniqueness
