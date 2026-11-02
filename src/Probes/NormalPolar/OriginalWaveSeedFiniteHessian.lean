import NormalPolar.OriginalWaveSeedFiniteResponse
import GlobalEmbedding.Paper.IncrementsJointSpatialJets

/-! Finite native Hessian assembly on the literal original parameter space.
All spatial and parameter derivative interchanges come from joint
regularity on the unchanged observer domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation

variable {X Y J : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
private local instance finiteHessianSemi : SeminormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance finiteHessianNorm : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance finiteHessianSpace : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedSpace

theorem originalProbe_native_hessian_add
    (f g : X → Y) (x : X) (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f y+g y)) x =
      fderiv ℝ (fderiv ℝ f) x+fderiv ℝ (fderiv ℝ g) x := by
  have he : fderiv ℝ (fun y => f y+g y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y+fderiv ℝ g y) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hyf hyg
    exact fderiv_fun_add (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  exact fderiv_fun_add
    ((hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num))

theorem originalProbe_native_hessian_finset
    (s : Finset J) (f : J → X → Y) (x : X)
    (hf : ∀ j ∈ s, ContDiffAt ℝ 2 (f j) x) :
    fderiv ℝ (fderiv ℝ (fun y => ∑ j ∈ s, f j y)) x =
      ∑ j ∈ s, fderiv ℝ (fderiv ℝ (f j)) x := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro hf
    simp
  | @insert i s hi ih =>
    intro hf
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, ContDiffAt ℝ 2 (f j) x :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    rw [originalProbe_native_hessian_add _ _ x hfi (ContDiffAt.sum hfs),ih hfs]

theorem originalProbe_native_hessian_finite_response
    {r : ℕ} (count : Fin r → ℕ)
    (f : ∀ l, Fin (count l) → ProbeParameters 1 → X → Y)
    (O : Set X) (hO : IsOpen O)
    (hjoint : ∀ l s, ContDiffOn ℝ ∞ (Function.uncurry (f l s)) (univ ×ˢ O))
    (u : ProbeParameters r) (x : X) (hx : x ∈ O) (k : Fin r) (sine : Bool) :
    fderiv ℝ (fun v : ProbeParameters r => fderiv ℝ (fderiv ℝ
      (fun y => ∑ l, ∑ s, f l s (originalProbePairProjection l v) y)) x)
      u (Pi.single (k,sine) 1) =
      ∑ s, fderiv ℝ (fun v : ProbeParameters 1 => fderiv ℝ (fderiv ℝ (f k s v)) x)
        (originalProbePairProjection k u) (Pi.single ((0 : Fin 1),sine) 1) := by
  have hspatial (l : Fin r) (s : Fin (count l)) (v : ProbeParameters 1) :
      ContDiffAt ℝ 2 (f l s v) x :=
    (((hjoint l s).contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ _,hx⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
  have he : (fun v : ProbeParameters r => fderiv ℝ (fderiv ℝ
      (fun y => ∑ l, ∑ s, f l s (originalProbePairProjection l v) y)) x) =
      (fun v : ProbeParameters r => ∑ l, ∑ s,
        fderiv ℝ (fderiv ℝ (f l s (originalProbePairProjection l v))) x) := by
    funext v
    rw [originalProbe_native_hessian_finset Finset.univ
      (fun l y => ∑ s, f l s (originalProbePairProjection l v) y) x
      (fun l _ => ContDiffAt.sum (fun s _ => hspatial l s _))]
    apply Finset.sum_congr rfl
    intro l _
    exact originalProbe_native_hessian_finset Finset.univ
      (fun s y => f l s (originalProbePairProjection l v) y) x (fun s _ => hspatial l s _)
  rw [he]
  apply originalProbePair_finite_response count
    (fun l s v => fderiv ℝ (fderiv ℝ (f l s v)) x) u
  intro l s
  have hj := (incrementsJointSpatialJets_bridge (Function.uncurry (f l s))
    (univ ×ˢ O) (isOpen_univ.prod hO) (hjoint l s)).2.2
  exact ((hj.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ _,hx⟩)).comp
    (originalProbePairProjection l u) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.originalProbe_native_hessian_finset
#print axioms GlobalEmbedding.NormalPolar.originalProbe_native_hessian_finite_response

