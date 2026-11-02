import GlobalEmbedding.Paper.BalancedNativeLocalSourceData
import GlobalEmbedding.Paper.BalancedNativeSourcePullback
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusChartFixedValues
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusValueLift
import GlobalEmbedding.Paper.BalancedNativeChartGluingOnOpen
import GlobalEmbedding.Paper.CollarLittleHolderEvaluation
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Actual selected principal-torus branches glue on the original common interval

Source: `main.tex`, `lem:balanced`, line418. Genuine global source values and actual
strict-small fixed equations imply compatibility; compatibility is not an input.
The already proved native open-domain gluing theorem supplies the global correction.
-/

noncomputable section
open Set WithLp IsManifold
open scoped Manifold ContDiff Topology
namespace GlobalEmbedding.Paper
local instance balancedNativeBranchTorusAtlas (a : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin a)) (PeriodOneTorus a) :=
  periodicFlatTorusChartedSpace a
local instance balancedNativeBranchTorusManifold (a : ℕ) :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) ∞ (PeriodOneTorus a) :=
  periodic_flat_torus_isManifold a ∞

/-- The actual torus value of a scalar multiple is that scalar times the original value. -/
theorem balanced_torusValue_smul {a N k : ℕ} {α : ℝ} (t : ℝ)
    (v : LittlePeriodicCAlphaFunction a N k α) (q : PeriodOneTorus a) :
    littlePeriodicCAlphaTorusValue (t • v) q = t • littlePeriodicCAlphaTorusValue v q := by
  obtain ⟨ev, hev, _⟩ := collar_little_holder_evaluation (a := a) (N := N) (k := k) (α := α) 0
  unfold littlePeriodicCAlphaTorusValue
  rw [← hev, ← hev, map_smul, map_smul]

variable {E H EB M B ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
namespace PrincipalTorusBundle
variable {a : ℕ} {I : ModelWithCorners ℝ E H} {π : M → B}
  [IsManifold I ∞ M] [AddAction (PeriodOneTorus a) M]
  (S : PrincipalTorusBundle (ι := ι) a I 𝓘(ℝ, EB) π)
include S

/-- Genuine source data and actual strict-small branch equations force actual native values
on overlaps to agree. This composes source transport with strict-small uniqueness. -/
theorem strict_small_branch_values_compatible {R N k : ℕ} {α : ℝ}
    (Q : LittlePeriodicCAlphaFunction a N k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α →L[ℝ] LittlePeriodicCAlphaFunction a R k α)
    (hQsym : ∀ v w, Q v w = Q w v)
    (hQτ : ∀ h v w, Q (littlePeriodicCAlphaTranslateIsometry h v)
      (littlePeriodicCAlphaTranslateIsometry h w) =
        littlePeriodicCAlphaTranslateIsometry h (Q v w))
    (i j : ι) (x : M) (hi : x ∈ (S.trivialization i).source)
    (hj : x ∈ (S.trivialization j).source)
    (sourceA : M → EuclideanSpace ℝ (Fin R) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (sourcef : M → EuclideanSpace ℝ (Fin N))
    (f₁ f₂ v₁ v₂ : LittlePeriodicCAlphaFunction a N k α)
    (A₁ A₂ : LittlePeriodicCAlphaFunction a R k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α)
    (hf₁ : ∀ y, f₁.val.toFun y = sourcef (S.fiberEuclideanLift i (π x) y))
    (hf₂ : ∀ y, f₂.val.toFun y = sourcef (S.fiberEuclideanLift j (π x) y))
    (hA₁ : ∀ u y, (A₁ u).val.toFun y =
      sourceA (S.fiberEuclideanLift i (π x) y) (u.val.toFun y))
    (hA₂ : ∀ u y, (A₂ u).val.toFun y =
      sourceA (S.fiberEuclideanLift j (π x) y) (u.val.toFun y))
    (hv₁ : v₁ = f₁ + A₁ (Q v₁ v₁)) (hv₂ : v₂ = f₂ + A₂ (Q v₂ v₂))
    (hs₁ : ‖(2 : ℝ) • A₁.comp (Q v₁)‖ < 1)
    (hs₂ : ‖(2 : ℝ) • A₂.comp (Q v₂)‖ < 1) :
    littlePeriodicCAlphaTorusValue v₁ (S.trivialization i x).2 =
      littlePeriodicCAlphaTorusValue v₂ (S.trivialization j x).2 := by
  have hbi := (S.trivialization i).mem_source.mp hi
  have hbj := (S.trivialization j).mem_source.mp hj
  obtain ⟨hf, hA⟩ := S.source_little_data_overlap i j hbi hbj sourceA sourcef
    f₁ f₂ A₁ A₂ hf₁ hf₂ hA₁ hA₂
  have hpoint : S.fiberChartPoint i (π x) (S.trivialization i x).2 = x := by
    change (S.trivialization i).toOpenPartialHomeomorph.symm _ = x
    have he : (π x, (S.trivialization i x).2) = S.trivialization i x :=
      Prod.ext ((S.trivialization i).coe_fst hi).symm rfl
    rw [he]
    exact (S.trivialization i).toOpenPartialHomeomorph.left_inv hi
  have hshift := congrArg Prod.snd (S.overlap_chart i j hbi hbj (S.trivialization i x).2)
  rw [hpoint] at hshift
  dsimp only at hshift
  have ht := littlePeriodicCAlpha_torus_chart_fixed_values Q hQsym hQτ A₁ f₁ v₁ v₂
    (S.overlapShift i j (π x)) hv₁ hs₁
  dsimp only at ht
  have hw := hv₂
  rw [hf, hA] at hw
  have hs := hs₂
  rw [hA] at hs
  have he := ht hw hs (S.trivialization i x).2
  rw [← hshift] at he
  exact he.symm

/-- Actual selected strict-small branches on a covering family of native patches glue to
an actual jointly smooth correction on the original common interval. Every chart expression
and every complete Euclidean fiber-lift expression is retained. Source transport and local
compatibility are derived from the same global source functions, not assumed. -/
theorem selected_native_branches_glue {κ : Type*} {R N : ℕ} {α : ℝ}
    (index : κ → ι) (center : κ → B) (V : κ → Set EB)
    (hV : ∀ k, IsOpen (V k))
    (hVU : ∀ k, V k ⊆ S.nativeBundleBaseSet (index k) (center k))
    (hcover : ∀ x : M, ∃ k, x ∈ (S.nativeBundleChart (index k) (center k)).source ∧
      (chartAt EB (center k)) (π x) ∈ V k)
    (δ : ℝ)
    (Q : LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a R 2 α)
    (hQsym : ∀ v w, Q v w = Q w v)
    (hQτ : ∀ h v w, Q (littlePeriodicCAlphaTranslateIsometry h v)
      (littlePeriodicCAlphaTranslateIsometry h w) =
        littlePeriodicCAlphaTranslateIsometry h (Q v w))
    (sourceA : ℝ × M → EuclideanSpace ℝ (Fin R) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (sourcef : ℝ × M → EuclideanSpace ℝ (Fin N))
    (f v : κ → EB × ℝ → LittlePeriodicCAlphaFunction a N 2 α)
    (A : κ → EB × ℝ → LittlePeriodicCAlphaFunction a R 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α)
    (hf : ∀ k z, z ∈ V k ×ˢ Metric.ball (0 : ℝ) δ → ∀ y,
      (f k z).val.toFun y = S.nativeSourcePullback sourcef (index k) (center k) z y)
    (hA : ∀ k z, z ∈ V k ×ˢ Metric.ball (0 : ℝ) δ → ∀ u y,
      (A k z u).val.toFun y = S.nativeSourcePullback sourceA (index k) (center k) z y
        (u.val.toFun y))
    (hfixed : ∀ k z, z ∈ V k ×ˢ Metric.ball (0 : ℝ) δ →
      v k z = f k z + A k z (Q (v k z) (v k z)))
    (hsmall : ∀ k z, z ∈ V k ×ˢ Metric.ball (0 : ℝ) δ →
      ‖(2 : ℝ) • (A k z).comp (Q (v k z))‖ < 1)
    (hsmooth : ∀ k, ContMDiffOn
      (𝓘(ℝ, EB × ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (fun z : (EB × ℝ) × PeriodOneTorus a ↦
        littlePeriodicCAlphaTorusValue (z.1.2 • v k z.1) z.2)
      ((V k ×ˢ Metric.ball (0 : ℝ) δ) ×ˢ univ)) :
    ∃ U : ℝ × M → EuclideanSpace ℝ (Fin N),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U
        (Metric.ball (0 : ℝ) δ ×ˢ univ) ∧
      (∀ k t x, t ∈ Metric.ball (0 : ℝ) δ →
        x ∈ (S.nativeBundleChart (index k) (center k)).source →
        (chartAt EB (center k)) (π x) ∈ V k →
        U (t, x) = littlePeriodicCAlphaTorusValue
          (t • v k ((chartAt EB (center k)) (π x), t)) (S.trivialization (index k) x).2) ∧
      ∀ k p, p ∈ V k → ∀ t, t ∈ Metric.ball (0 : ℝ) δ →
        ∀ y : EuclideanSpace ℝ (Fin a),
          U (t, S.fiberEuclideanLift (index k) ((chartAt EB (center k)).symm p) y) =
            (t • v k (p, t)).val.toFun y := by
  let e := fun k ↦ S.nativeBundleChart (index k) (center k)
  let Ω := fun k ↦ (e k).source ∩ (e k) ⁻¹' (V k ×ˢ univ)
  let patch := fun k ↦ Metric.ball (0 : ℝ) δ ×ˢ Ω k
  have hΩ (k : κ) : IsOpen (Ω k) :=
    (e k).isOpen_inter_preimage ((hV k).prod isOpen_univ)
  have hpatch (k : κ) : IsOpen (patch k) := Metric.isOpen_ball.prod (hΩ k)
  have htriv (k : κ) (x : M) (hx : x ∈ (e k).source) :
      x ∈ (S.trivialization (index k)).source := by
    rw [S.nativeBundleChart_source] at hx
    exact hx.1
  have hcoord (k : κ) (x : M) (hx : x ∈ (e k).source) :
      e k x = ((chartAt EB (center k)) (π x), (S.trivialization (index k) x).2) :=
    S.nativeBundleChart_apply (index k) (center k) (htriv k x hx)
  have hbase (k : κ) (x : M) (hx : x ∈ (e k).source) :
      (chartAt EB (center k)).symm (e k x).1 = π x := by
    rw [hcoord k x hx]
    have hs := hx
    rw [S.nativeBundleChart_source] at hs
    exact (chartAt EB (center k)).left_inv hs.2
  let localValue := fun k (z : ℝ × M) ↦ littlePeriodicCAlphaTorusValue
    (z.1 • v k ((e k z.2).1, z.1)) (e k z.2).2
  have hlocal (k : κ) : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (localValue k) (patch k) := by
    have hc : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
        (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) ∞
        (fun z : ℝ × M ↦ e k z.2) (patch k) :=
      (S.contMDiffOn_nativeBundleChart (index k) (center k)).comp
        contMDiff_snd.contMDiffOn (fun z hz ↦ hz.2.1)
    have hp : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, EB × ℝ) ∞
        (fun z : ℝ × M ↦ ((e k z.2).1, z.1)) (patch k) :=
      (contMDiff_fst.comp_contMDiffOn hc).prodMk_space
        (contMDiff_fst.contMDiffOn (s := patch k))
    have hq : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
        𝓘(ℝ, EuclideanSpace ℝ (Fin a)) ∞
        (fun z : ℝ × M ↦ (e k z.2).2) (patch k) :=
      contMDiff_snd.comp_contMDiffOn hc
    have hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
        (𝓘(ℝ, EB × ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) ∞
        (fun z : ℝ × M ↦ (((e k z.2).1, z.1), (e k z.2).2)) (patch k) :=
      hp.prodMk hq
    have hmap : MapsTo
        (fun z : ℝ × M ↦ (((e k z.2).1, z.1), (e k z.2).2)) (patch k)
        ((V k ×ˢ Metric.ball (0 : ℝ) δ) ×ˢ (univ : Set (PeriodOneTorus a))) := by
      intro z hz
      exact ⟨⟨hz.2.2.1, hz.1⟩, mem_univ _⟩
    have hcomp := ContMDiffOn.comp
      (I := 𝓘(ℝ, ℝ).prod I)
      (I' := 𝓘(ℝ, EB × ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a)))
      (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin N)))
      (hsmooth k) hg hmap
    exact hcomp
  have hcompat (k l : κ) (z : ℝ × M) (hk : z ∈ patch k) (hl : z ∈ patch l) :
      localValue k z = localValue l z := by
    have hpk : ((e k z.2).1, z.1) ∈ V k ×ˢ Metric.ball (0 : ℝ) δ :=
      ⟨hk.2.2.1, hk.1⟩
    have hpl : ((e l z.2).1, z.1) ∈ V l ×ˢ Metric.ball (0 : ℝ) δ :=
      ⟨hl.2.2.1, hl.1⟩
    have hfv (k : κ) (hk : z ∈ patch k) (u : LittlePeriodicCAlphaFunction a R 2 α)
        (y : EuclideanSpace ℝ (Fin a)) :
        (A k ((e k z.2).1, z.1) u).val.toFun y =
          sourceA (z.1, S.fiberEuclideanLift (index k) (π z.2) y) (u.val.toFun y) := by
      have ht := hA k ((e k z.2).1, z.1) ⟨hk.2.2.1, hk.1⟩ u y
      dsimp only [nativeSourcePullback] at ht
      rw [hbase k z.2 hk.2.1] at ht
      exact ht
    have hff (k : κ) (hk : z ∈ patch k) (y : EuclideanSpace ℝ (Fin a)) :
        (f k ((e k z.2).1, z.1)).val.toFun y =
          sourcef (z.1, S.fiberEuclideanLift (index k) (π z.2) y) := by
      have ht := hf k ((e k z.2).1, z.1) ⟨hk.2.2.1, hk.1⟩ y
      dsimp only [nativeSourcePullback] at ht
      rw [hbase k z.2 hk.2.1] at ht
      exact ht
    have ht := S.strict_small_branch_values_compatible Q hQsym hQτ (index k) (index l) z.2
      (htriv k z.2 hk.2.1) (htriv l z.2 hl.2.1)
      (fun x ↦ sourceA (z.1, x)) (fun x ↦ sourcef (z.1, x))
      (f k ((e k z.2).1, z.1)) (f l ((e l z.2).1, z.1))
      (v k ((e k z.2).1, z.1)) (v l ((e l z.2).1, z.1))
      (A k ((e k z.2).1, z.1)) (A l ((e l z.2).1, z.1))
      (hff k hk) (hff l hl) (hfv k hk) (hfv l hl)
      (hfixed k _ hpk) (hfixed l _ hpl) (hsmall k _ hpk) (hsmall l _ hpl)
    change littlePeriodicCAlphaTorusValue (z.1 • v k _) (e k z.2).2 =
      littlePeriodicCAlphaTorusValue (z.1 • v l _) (e l z.2).2
    rw [balanced_torusValue_smul, balanced_torusValue_smul,
      hcoord k z.2 hk.2.1, hcoord l z.2 hl.2.1]
    rw [hcoord k z.2 hk.2.1, hcoord l z.2 hl.2.1] at ht
    exact congrArg (fun w ↦ z.1 • w) ht
  let identityChart := fun k ↦ OpenPartialHomeomorph.ofSet (patch k) (hpatch k)
  obtain ⟨U, hU, hUvalue⟩ := balanced_native_chart_gluing_on_open
    (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
    (Metric.ball (0 : ℝ) δ ×ˢ univ) (Metric.isOpen_ball.prod isOpen_univ)
    identityChart localValue
    (by
      intro z hz
      obtain ⟨k, hx, hp⟩ := hcover z.2
      refine ⟨k, hz.1, hx, ?_, mem_univ _⟩
      rw [hcoord k z.2 hx]
      exact hp)
    (fun _ ↦ contMDiff_id.contMDiffOn) hlocal
    (fun k l z _ hk hl ↦ hcompat k l z hk hl)
  have hevery (k : κ) (t : ℝ) (x : M) (ht : t ∈ Metric.ball (0 : ℝ) δ)
      (hx : x ∈ (e k).source) (hp : (chartAt EB (center k)) (π x) ∈ V k) :
      U (t, x) = littlePeriodicCAlphaTorusValue
        (t • v k ((chartAt EB (center k)) (π x), t)) (S.trivialization (index k) x).2 := by
    have hz : (t, x) ∈ patch k := by
      refine ⟨ht, hx, ?_, mem_univ _⟩
      rw [hcoord k x hx]
      exact hp
    have hv := hUvalue k (t, x) ⟨ht, mem_univ x⟩ hz
    change U (t, x) = localValue k (t, x) at hv
    dsimp only [localValue] at hv
    rw [hcoord k x hx] at hv
    exact hv
  refine ⟨U, hU, hevery, ?_⟩
  intro k p hp t ht y
  have hb := hVU k hp
  have hproj : π (S.fiberEuclideanLift (index k) ((chartAt EB (center k)).symm p) y) =
      (chartAt EB (center k)).symm p :=
    S.projection_fiberChartPoint (index k) hb.2 _
  have hxtriv := S.fiberChartPoint_mem_source (index k) hb.2
    (toLp 2 (fun j ↦ (y j : AddCircle (1 : ℝ))))
  have hx : S.fiberEuclideanLift (index k) ((chartAt EB (center k)).symm p) y ∈
      (e k).source := by
    rw [S.nativeBundleChart_source]
    refine ⟨hxtriv, ?_⟩
    change π (S.fiberEuclideanLift (index k) ((chartAt EB (center k)).symm p) y) ∈
      (chartAt EB (center k)).source
    rw [hproj]
    exact (chartAt EB (center k)).map_target hb.1
  have hpc : (chartAt EB (center k))
      (π (S.fiberEuclideanLift (index k) ((chartAt EB (center k)).symm p) y)) = p := by
    rw [hproj]
    exact (chartAt EB (center k)).right_inv hb.1
  have hv := hevery k t _ ht hx (hpc.symm ▸ hp)
  rw [hpc] at hv
  have hq := congrArg Prod.snd (S.chart_fiberChartPoint (index k) hb.2
    (toLp 2 (fun j ↦ (y j : AddCircle (1 : ℝ)))))
  change (S.trivialization (index k)
    (S.fiberEuclideanLift (index k) ((chartAt EB (center k)).symm p) y)).2 =
      toLp 2 (fun j ↦ (y j : AddCircle (1 : ℝ))) at hq
  rw [hq, littlePeriodicCAlphaTorusValue_lift] at hv
  exact hv

#print axioms selected_native_branches_glue
#print axioms balanced_torusValue_smul
#print axioms strict_small_branch_values_compatible
end PrincipalTorusBundle
end GlobalEmbedding.Paper
