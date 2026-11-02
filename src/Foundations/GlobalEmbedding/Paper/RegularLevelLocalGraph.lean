import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual local graph of a finite-dimensional regular level

Source: `literature/parallelizable-stable-plus-one/main.tex`, Lemma `lem:avoidance`,
proof line 940. The regular level is exactly the image of a smooth map from an
open subset of the actual derivative kernel. The native implicit chart has first
coordinate equal to the original equation. We restrict to a neighborhood where
its derivative stays invertible, so its fixed inverse is smooth everywhere used.
-/

open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

open Set Filter

/-- A smooth map with surjective actual derivative has its local zero level exactly
parametrized by an open subset of the derivative kernel. The kernel dimension is
the source dimension minus the target dimension by rank-nullity. Smoothness holds
on the whole open parameter set, and no positive-dimension or nonempty-coordinate
hypothesis is imposed. Source: the local regular-level step of `lem:avoidance`. -/
theorem regular_level_local_graph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    {x : E} (hx : x ∈ U) (hzero : f x = 0)
    (hsurj : Function.Surjective (fderiv ℝ f x)) :
    let K := (fderiv ℝ f x).ker
    Module.finrank ℝ K + Module.finrank ℝ F = Module.finrank ℝ E ∧
      ∃ (V : Set E) (W : Set K) (g : K → E),
        IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ IsOpen W ∧ (0 : K) ∈ W ∧
          ContDiffOn ℝ ∞ g W ∧ g '' W = V ∩ f ⁻¹' {0} := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : CompleteSpace F := FiniteDimensional.complete ℝ F
  dsimp only
  let d := fderiv ℝ f x
  have hrange : d.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := d.toLinearMap.finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at hdim
  refine ⟨by simpa only [d, add_comm] using hdim, ?_⟩
  have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
  have hstrict : HasStrictFDerivAt f d x := hfx.hasStrictFDerivAt (by simp)
  let hker := d.ker_closedComplemented_of_finiteDimensional_range
  let φ := hstrict.implicitFunctionDataOfComplemented f d hrange hker
  let T := φ.prodFun
  let e := φ.toOpenPartialHomeomorph
  have hT : ContDiffOn ℝ ∞ T U := by
    change ContDiffOn ℝ ∞ (fun y ↦ (f y, (Classical.choose hker) (y - x))) U
    exact hf.prodMk
      (((Classical.choose hker).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)
  have hxsource : x ∈ e.source := φ.pt_mem_toOpenPartialHomeomorph_source
  have hTx : ContDiffAt ℝ ∞ T x := hT.contDiffAt (hU.mem_nhds hx)
  have hgood : ∀ᶠ y in 𝓝 x, (fderiv ℝ T y).IsInvertible :=
    hTx.continuousAt_fderiv (by simp) φ.isInvertible_fderiv_prodFun.eventually_nhds
  have hnhds : {y | y ∈ U ∧ y ∈ e.source ∧ (fderiv ℝ T y).IsInvertible} ∈ 𝓝 x :=
    inter_mem (hU.mem_nhds hx) (inter_mem (e.open_source.mem_nhds hxsource) hgood)
  obtain ⟨S, hSsub, hSopen, hxS⟩ := mem_nhds_iff.mp hnhds
  let er := e.restrOpen S hSopen
  let slice : d.ker → F × d.ker := fun z ↦ (0, z)
  let W := slice ⁻¹' er.target
  let g : d.ker → E := fun z ↦ er.symm (slice z)
  have hslice : ContDiff ℝ ∞ slice := contDiff_const.prodMk contDiff_id
  have hxV : x ∈ er.source := ⟨hxsource, hxS⟩
  have heX : er x = (0, (0 : d.ker)) := by
    change (f x, (Classical.choose hker) (x - x)) = (0, 0)
    simp [hzero]
  have hWopen : IsOpen W := er.open_target.preimage hslice.continuous
  have h0W : (0 : d.ker) ∈ W := by
    change (0, (0 : d.ker)) ∈ er.target
    rw [← heX]
    exact er.map_source hxV
  have hg : ContDiffOn ℝ ∞ g W := by
    intro z hz
    have hyV : g z ∈ er.source := er.map_target hz
    have hy := hSsub hyV.2
    have hTy : ContDiffAt ℝ ∞ T (g z) := hT.contDiffAt (hU.mem_nhds hy.1)
    obtain ⟨L, hL⟩ := hy.2.2
    have hdy : HasFDerivAt T (L : E →L[ℝ] F × d.ker) (g z) := by
      rw [hL]
      exact (hTy.differentiableAt (by simp)).hasFDerivAt
    have hInv : ContDiffAt ℝ ∞ er.symm (slice z) := er.contDiffAt_symm hz hdy hTy
    exact (hInv.comp z hslice.contDiffAt).contDiffWithinAt
  refine ⟨er.source, W, g, er.open_source, hxV, ?_, hWopen, h0W, hg, ?_⟩
  · intro y hy
    exact (hSsub hy.2).1
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨er.map_target hz, ?_⟩
      have hr := congrArg Prod.fst (er.right_inv hz)
      change f (g z) = 0 at hr
      exact hr
    · rintro ⟨hyV, hyzero⟩
      let z := (er y).2
      have hcoord : slice z = er y := by
        apply Prod.ext
        · change 0 = f y
          exact hyzero.symm
        · rfl
      refine ⟨z, ?_, ?_⟩
      · change slice z ∈ er.target
        rw [hcoord]
        exact er.map_source hyV
      · change er.symm (slice z) = y
        rw [hcoord]
        exact er.left_inv hyV

/-- Euclidean-coordinate form of the regular-level graph: full rank `k` gives
an open parameter set in `ℝ^(m-k)`, including `k=m` and empty coordinate types.
Source: the regular-level graph step in `lem:avoidance`, proof line 940. -/
theorem regular_level_local_graph_euclidean
    {m k : ℕ} {U : Set (Fin m → ℝ)} (hU : IsOpen U)
    {f : (Fin m → ℝ) → (Fin k → ℝ)} (hf : ContDiffOn ℝ ∞ f U)
    {x : Fin m → ℝ} (hx : x ∈ U) (hzero : f x = 0)
    (hrank : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = k) :
    k ≤ m ∧ ∃ (V : Set (Fin m → ℝ)) (W : Set (Fin (m-k) → ℝ))
      (g : (Fin (m-k) → ℝ) → (Fin m → ℝ)),
        IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ IsOpen W ∧ (0 : Fin (m-k) → ℝ) ∈ W ∧
          ContDiffOn ℝ ∞ g W ∧ g '' W = V ∩ f ⁻¹' {0} := by
  have hsurj : Function.Surjective (fderiv ℝ f x) := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Module.finrank_fin_fun] using hrank
  obtain ⟨hdim, V, W, g, hVo, hxV, hVU, hWo, h0W, hg, him⟩ :=
    regular_level_local_graph hU hf hx hzero hsurj
  let K := (fderiv ℝ f x).ker
  have hdim' : Module.finrank ℝ K + k = m := by
    simpa only [Module.finrank_fin_fun] using hdim
  have hK : Module.finrank ℝ (Fin (m-k) → ℝ) = Module.finrank ℝ K := by
    rw [Module.finrank_fin_fun]
    omega
  let c : (Fin (m-k) → ℝ) ≃L[ℝ] K := ContinuousLinearEquiv.ofFinrankEq hK
  refine ⟨by omega, V, c ⁻¹' W, g ∘ c, hVo, hxV, hVU,
    hWo.preimage c.continuous, ?_, ?_, ?_⟩
  · change c 0 ∈ W
    simpa only [map_zero] using h0W
  · exact hg.comp c.contDiff.contDiffOn (fun _ hz ↦ hz)
  · rw [Set.image_comp, Set.image_preimage_eq _ c.surjective, him]

#print axioms regular_level_local_graph_euclidean

#print axioms regular_level_local_graph

end GlobalEmbedding.Paper
