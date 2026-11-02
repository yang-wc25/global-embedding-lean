import GlobalEmbedding.Paper.IncrementsGlobalPrimaryMeanBinding

/-! The literal finite primary differential construction is local in the
physical parameter.  Equality of source slices and computational primitive
fields at that parameter is sufficient; global equality of base maps or
heterogeneous equality of primary families is unnecessary. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Manifold Set
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Label Sub : Type*} [Fintype Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem fullIncrementNov_mode_source_congr
    (f f' : M → V) (hf : ContMDiff I 𝓘(ℝ,V) ∞ f) (hf' : ContMDiff I 𝓘(ℝ,V) ∞ f')
    (c c' : D → M) (hfEq : f = f') (hcEq : c = c')
    (forcing : D → Fin (m+1) → Fin (m+1) → ℝ)
    (vf : (x : D) → normalSpace (I := I) f (c x))
    (vf' : (x : D) → normalSpace (I := I) f' (c' x))
    (hv : ∀ x, (vf x : V) = (vf' x : V)) :
    incrementsModeSource f hf c forcing vf = incrementsModeSource f' hf' c' forcing vf' := by
  subst f'
  subst c'
  have hvEq : vf = vf' := funext (fun x => Subtype.ext (hv x))
  subst vf'
  rfl

theorem fullIncrementNov_mode_firstOrder_congr
    (f f' : M → V) (hf : ContMDiff I 𝓘(ℝ,V) ∞ f) (hf' : ContMDiff I 𝓘(ℝ,V) ∞ f')
    (c c' : D → M) (hfEq : f = f') (hcEq : c = c') :
    incrementsModeComplexFirstOrderA f hf c = incrementsModeComplexFirstOrderA f' hf' c' ∧
    incrementsModeComplexFirstOrderB f hf c = incrementsModeComplexFirstOrderB f' hf' c' := by
  subst f'
  subst c'
  exact ⟨rfl,rfl⟩

theorem fullIncrementNov_mode_fullReconstruction_congr
    (f f' : M → V) (hf : ContMDiff I 𝓘(ℝ,V) ∞ f) (hf' : ContMDiff I 𝓘(ℝ,V) ∞ f')
    (c c' : D → M) (hfEq : f = f') (hcEq : c = c')
    (u u' : D → D) (hu : u = u') (forcing : D → Fin (m+1) → Fin (m+1) → ℝ)
    (vf : (x : D) → normalSpace (I := I) f (c x))
    (vf' : (x : D) → normalSpace (I := I) f' (c' x))
    (hv : ∀ x, (vf x : V) = (vf' x : V)) :
    incrementsModeFullReconstruction f hf c u forcing vf =
      incrementsModeFullReconstruction f' hf' c' u' forcing vf' := by
  subst f'
  subst c'
  subst u'
  have hvEq : vf = vf' := funext (fun x => Subtype.ext (hv x))
  subst vf'
  rfl

theorem fullIncrementNov_primary_localFree_value_congr
    (F F' : Ep → M → V)
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (Λ := Label) (Β := Sub) F)
    (g' : IncrementsGlobalPrimaryFamily (I := I) (m := m) (Λ := Label) (Β := Sub) F')
    (input input' : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (tau : ℝ) (nu : Label) (beta : Sub) (t : Ep)
    (hInput : input t = input' t)
    (hCut : ∀ x, g.cutoff nu (t,x) = g'.cutoff nu (t,x))
    (hNormal : ∀ x, g.normal nu (t,x) = g'.normal nu (t,x))
    (hLinear : ∀ x, g.linearArgument nu t x = g'.linearArgument nu t x)
    (hEta : ∀ x, g.eta nu beta (t,x) = g'.eta nu beta (t,x))
    (hTarget : ∀ x, (t,x) ∈ (g.chart nu beta).target ↔ (t,x) ∈ (g'.chart nu beta).target)
    (hInverse : g.inverse nu beta t = g'.inverse nu beta t) (x : D) :
    (incrementsGlobalPrimaryLocalFree F g input tau nu beta t x : V) =
      (incrementsGlobalPrimaryLocalFree F' g' input' tau nu beta t x : V) := by
  classical
  have hArg : g.linearArgument nu t (g.inverse nu beta t x) (input t (g.inverse nu beta t x)) =
      g'.linearArgument nu t (g'.inverse nu beta t x) (input' t (g'.inverse nu beta t x)) := by
    rw [hLinear,hInput]
    exact congrArg (fun y => g'.linearArgument nu t y (input' t y)) (congrFun hInverse x)
  unfold incrementsGlobalPrimaryLocalFree incrementsGlobalPrimaryB
  by_cases hx : (t,x) ∈ (g.chart nu beta).target
  · simp only [hx,(hTarget x).mp hx,dite_true,Submodule.coe_smul_of_tower]
    simp only [hArg,hInverse,hCut,hNormal,hEta]
  · simp only [hx,not_congr (hTarget x) |>.mp hx,dite_false,Submodule.coe_zero]

theorem fullIncrementNov_primary_source_congr
    (F F' : Ep → M → V)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (hF' : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F' p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (Λ := Label) (Β := Sub) F)
    (g' : IncrementsGlobalPrimaryFamily (I := I) (m := m) (Λ := Label) (Β := Sub) F')
    (input input' : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (tau : ℝ) (nu : Label) (beta : Sub) (t : Ep) (hFt : F t = F' t)
    (hInput : input t = input' t)
    (hCut : ∀ x, g.cutoff nu (t,x) = g'.cutoff nu (t,x))
    (hNormal : ∀ x, g.normal nu (t,x) = g'.normal nu (t,x))
    (hLinear : ∀ x, g.linearArgument nu t x = g'.linearArgument nu t x)
    (hEta : ∀ x, g.eta nu beta (t,x) = g'.eta nu beta (t,x))
    (hTarget : ∀ x, (t,x) ∈ (g.chart nu beta).target ↔ (t,x) ∈ (g'.chart nu beta).target)
    (hInverse : g.inverse nu beta t = g'.inverse nu beta t) (x : D) :
    incrementsGlobalPrimarySource F hF g input tau nu beta (t,x) =
      incrementsGlobalPrimarySource F' hF' g' input' tau nu beta (t,x) := by
  have hFree := fullIncrementNov_primary_localFree_value_congr F F' g g' input input'
    tau nu beta t hInput hCut hNormal hLinear hEta hTarget hInverse
  have hSource := fullIncrementNov_mode_source_congr (F t) (F' t) (hF t) (hF' t)
    (g.inverse nu beta t) (g'.inverse nu beta t) hFt hInverse (fun _ _ _ => 0)
    (incrementsGlobalPrimaryLocalFree F g input tau nu beta t)
    (incrementsGlobalPrimaryLocalFree F' g' input' tau nu beta t) hFree
  exact congrArg incrementsModeComplexInclude (congrFun hSource x)

theorem fullIncrementNov_primary_finiteU_congr
    (F F' : Ep → M → V)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (hF' : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F' p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (Λ := Label) (Β := Sub) F)
    (g' : IncrementsGlobalPrimaryFamily (I := I) (m := m) (Λ := Label) (Β := Sub) F')
    (input input' : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (nu : Label) (beta : Sub) (t : Ep) (hFt : F t = F' t)
    (hInput : input t = input' t)
    (hCut : ∀ x, g.cutoff nu (t,x) = g'.cutoff nu (t,x))
    (hNormal : ∀ x, g.normal nu (t,x) = g'.normal nu (t,x))
    (hLinear : ∀ x, g.linearArgument nu t x = g'.linearArgument nu t x)
    (hEta : ∀ x, g.eta nu beta (t,x) = g'.eta nu beta (t,x))
    (hTarget : ∀ x, (t,x) ∈ (g.chart nu beta).target ↔ (t,x) ∈ (g'.chart nu beta).target)
    (hInverse : g.inverse nu beta t = g'.inverse nu beta t) :
    incrementsGlobalPrimaryFiniteU F hF g input length tau nu beta t =
      incrementsGlobalPrimaryFiniteU F' hF' g' input' length tau nu beta t := by
  have hSource := funext (fullIncrementNov_primary_source_congr F F' hF hF' g g' input input'
    tau nu beta t hFt hInput hCut hNormal hLinear hEta hTarget hInverse)
  have hAB := fullIncrementNov_mode_firstOrder_congr (F t) (F' t) (hF t) (hF' t)
    (g.inverse nu beta t) (g'.inverse nu beta t) hFt hInverse
  simp only [incrementsGlobalPrimaryFiniteU,hSource,hAB.1,hAB.2]

theorem fullIncrementNov_primary_localZ_congr
    (F F' : Ep → M → V)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (hF' : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F' p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (Λ := Label) (Β := Sub) F)
    (g' : IncrementsGlobalPrimaryFamily (I := I) (m := m) (Λ := Label) (Β := Sub) F')
    (input input' : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (channel : Bool) (nu : Label) (beta : Sub) (t : Ep) (hFt : F t = F' t)
    (hInput : input t = input' t)
    (hCut : ∀ x, g.cutoff nu (t,x) = g'.cutoff nu (t,x))
    (hNormal : ∀ x, g.normal nu (t,x) = g'.normal nu (t,x))
    (hLinear : ∀ x, g.linearArgument nu t x = g'.linearArgument nu t x)
    (hEta : ∀ x, g.eta nu beta (t,x) = g'.eta nu beta (t,x))
    (hTarget : ∀ x, (t,x) ∈ (g.chart nu beta).target ↔ (t,x) ∈ (g'.chart nu beta).target)
    (hInverse : g.inverse nu beta t = g'.inverse nu beta t) (x : D) :
    incrementsGlobalPrimaryLocalZ F hF g input length tau channel nu beta (t,x) =
      incrementsGlobalPrimaryLocalZ F' hF' g' input' length tau channel nu beta (t,x) := by
  have hU := fullIncrementNov_primary_finiteU_congr F F' hF hF' g g' input input'
    length tau nu beta t hFt hInput hCut hNormal hLinear hEta hTarget hInverse
  have hFree := fullIncrementNov_primary_localFree_value_congr F F' g g' input input'
    tau nu beta t hInput hCut hNormal hLinear hEta hTarget hInverse
  unfold incrementsGlobalPrimaryLocalZ
  apply congrFun (fullIncrementNov_mode_fullReconstruction_congr (F t) (F' t) (hF t) (hF' t)
    (g.inverse nu beta t) (g'.inverse nu beta t) hFt hInverse _ _ ?_ (fun _ _ _ => 0) _ _ ?_) x
  · simp only [hU]
  · intro y
    cases channel <;> simp only [Bool.false_eq_true,ite_false,ite_true,Submodule.coe_zero,hFree]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNov_primary_localFree_value_congr
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_primary_source_congr
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_primary_finiteU_congr
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_primary_localZ_congr
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_mode_source_congr
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_mode_firstOrder_congr
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_mode_fullReconstruction_congr
