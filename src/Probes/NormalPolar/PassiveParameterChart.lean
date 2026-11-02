import Probes.Round3ParameterChartPullback

/-!
# Adding a passive parameter to an actual single-parameter chart

The seed parameter space has one point (the application is `EuclideanSpace ℝ
(Fin 0)`).  Every source chart on its product with the spatial manifold has a
literal extension to a product with an arbitrary topological parameter space.
The extension keeps exactly the old spatial source and target, and its first
coordinate is the identity.  No identity of completed waves is an input.
-/

noncomputable section
open Set Function
namespace GlobalEmbedding.Continuation

variable {S P M D : Type*}
  [TopologicalSpace S] [Subsingleton S] [TopologicalSpace P]
  [TopologicalSpace M] [TopologicalSpace D]

/-- A one-point seed chart necessarily preserves its parameter. -/
theorem passiveParameterSeedChart_preserves
    (a : OpenPartialHomeomorph (S × M) (S × D)) :
    Round3ParameterChartPreserves a := fun _ _ => Subsingleton.elim _ _

/-- The actual chart with its new passive parameter unchanged. -/
def passiveParameterChart (s₀ : S)
    (a : OpenPartialHomeomorph (S × M) (S × D)) :
    OpenPartialHomeomorph (P × M) (P × D) where
  toFun z := (z.1, (a (s₀, z.2)).2)
  invFun z := (z.1, (a.symm (s₀, z.2)).2)
  source := (fun z : P × M => (s₀, z.2)) ⁻¹' a.source
  target := (fun z : P × D => (s₀, z.2)) ⁻¹' a.target
  map_source' := by
    intro z hz
    have h : (s₀, (a (s₀, z.2)).2) = a (s₀, z.2) :=
      Prod.ext (Subsingleton.elim _ _) rfl
    change (s₀, (a (s₀, z.2)).2) ∈ a.target
    rw [h]
    exact a.map_source hz
  map_target' := by
    intro z hz
    have h : (s₀, (a.symm (s₀, z.2)).2) = a.symm (s₀, z.2) :=
      Prod.ext (Subsingleton.elim _ _) rfl
    change (s₀, (a.symm (s₀, z.2)).2) ∈ a.source
    rw [h]
    exact a.map_target hz
  left_inv' := by
    intro z hz
    apply Prod.ext
    · rfl
    · have h : (s₀, (a (s₀, z.2)).2) = a (s₀, z.2) :=
        Prod.ext (Subsingleton.elim _ _) rfl
      change (a.symm (s₀, (a (s₀, z.2)).2)).2 = z.2
      rw [h, a.left_inv hz]
  right_inv' := by
    intro z hz
    apply Prod.ext
    · rfl
    · have h : (s₀, (a.symm (s₀, z.2)).2) = a.symm (s₀, z.2) :=
        Prod.ext (Subsingleton.elim _ _) rfl
      change (a (s₀, (a.symm (s₀, z.2)).2)).2 = z.2
      rw [h, a.right_inv hz]
  continuousOn_toFun := continuous_fst.continuousOn.prodMk
    (a.continuousOn.comp (continuous_const.prodMk continuous_snd).continuousOn
      (fun _ h => h)).snd
  continuousOn_invFun := continuous_fst.continuousOn.prodMk
    (a.symm.continuousOn.comp (continuous_const.prodMk continuous_snd).continuousOn
      (fun _ h => h)).snd
  open_source := a.open_source.preimage (continuous_const.prodMk continuous_snd)
  open_target := a.open_target.preimage (continuous_const.prodMk continuous_snd)

@[simp] theorem passiveParameterChart_apply (s₀ : S)
    (a : OpenPartialHomeomorph (S × M) (S × D)) (z : P × M) :
    passiveParameterChart s₀ a z = (z.1, (a (s₀, z.2)).2) := rfl

@[simp] theorem passiveParameterChart_symm_apply (s₀ : S)
    (a : OpenPartialHomeomorph (S × M) (S × D)) (z : P × D) :
    (passiveParameterChart s₀ a).symm z = (z.1, (a.symm (s₀, z.2)).2) := rfl

@[simp] theorem passiveParameterChart_source (s₀ : S)
    (a : OpenPartialHomeomorph (S × M) (S × D)) (z : P × M) :
    z ∈ (passiveParameterChart s₀ a).source ↔ (s₀, z.2) ∈ a.source := Iff.rfl

@[simp] theorem passiveParameterChart_target (s₀ : S)
    (a : OpenPartialHomeomorph (S × M) (S × D)) (z : P × D) :
    z ∈ (passiveParameterChart s₀ a).target ↔ (s₀, z.2) ∈ a.target := Iff.rfl

theorem passiveParameterChart_preserves (s₀ : S)
    (a : OpenPartialHomeomorph (S × M) (S × D)) :
    Round3ParameterChartPreserves (passiveParameterChart (P := P) s₀ a) :=
  fun _ _ => rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveParameterChart
#print axioms GlobalEmbedding.Continuation.passiveParameterChart_preserves
