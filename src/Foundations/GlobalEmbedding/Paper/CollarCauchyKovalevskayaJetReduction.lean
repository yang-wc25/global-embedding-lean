import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import GlobalEmbedding.Paper.CollarCKAnalyticNormalization
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# First-order reduction of the analytic second-order Cauchy problem

Source: `literature/parallelizable-stable-plus-one/main.tex`, Theorem `thm:ck`;
reduction follows Gantumur, *Math 580 Lecture Notes 2*, Corollary 20, printed p. 11.
-/

open scoped Topology

namespace GlobalEmbedding.Paper

noncomputable section

abbrev CKX (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev CKVal (m : ℕ) := Fin m → ℝ
abbrev CKSpatial (n m : ℕ) := Fin n → CKVal m
abbrev CKHessian (n m : ℕ) := Fin n → Fin n → CKVal m
abbrev CKState (n m : ℕ) := CKVal m × (CKSpatial n m × CKVal m)
abbrev CKForcingInput (n m : ℕ) :=
  CKX n × (ℝ × (CKVal m × (CKSpatial n m ×
    (CKHessian n m × (CKVal m × CKSpatial n m)))))
abbrev CKFirstOrderInput (n m : ℕ) :=
  CKX n × (ℝ × (CKState n m × (Fin n → CKState n m)))

abbrev CKJoint (n : ℕ) := ℝ × CKX n

def ckTimeDirection {n : ℕ} : CKJoint n := (1, 0)

def ckSpaceDirection {n : ℕ} (i : Fin n) : CKJoint n :=
  (0, EuclideanSpace.single i (1 : ℝ))

def ckDataSpatialDerivative {n m : ℕ} (f : CKX n → CKVal m) (x : CKX n) : CKSpatial n m :=
  fun i => fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))

def ckDataSpatialHessian {n m : ℕ} (f : CKX n → CKVal m) (x : CKX n) : CKHessian n m :=
  fun i j => fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))) x
    (EuclideanSpace.single i (1 : ℝ))

def ckTimeDerivative {n m : ℕ} (u : CKJoint n → CKVal m) (z : CKJoint n) : CKVal m :=
  fderiv ℝ u z ckTimeDirection

def ckSpatialDerivative {n m : ℕ} (u : CKJoint n → CKVal m) (z : CKJoint n) : CKSpatial n m :=
  fun i => fderiv ℝ u z (ckSpaceDirection i)

def ckSecondTimeDerivative {n m : ℕ} (u : CKJoint n → CKVal m) (z : CKJoint n) : CKVal m :=
  fderiv ℝ (fun y => ckTimeDerivative u y) z ckTimeDirection

def ckSecondSpatialDerivative {n m : ℕ} (u : CKJoint n → CKVal m) (z : CKJoint n) : CKHessian n m :=
  fun i j => fderiv ℝ (fun y => fderiv ℝ u y (ckSpaceDirection j)) z (ckSpaceDirection i)

def ckMixedDerivative {n m : ℕ} (u : CKJoint n → CKVal m) (z : CKJoint n) : CKSpatial n m :=
  fun i => fderiv ℝ (fun y => ckTimeDerivative u y) z (ckSpaceDirection i)

def ckProlongedInitialData {n m : ℕ} (u₀ u₁ : CKX n → CKVal m) (x : CKX n) : CKState n m :=
  (u₀ x, (ckDataSpatialDerivative u₀ x, u₁ x))

def ckForcingInitialPoint {n m : ℕ}
    (u₀ u₁ : CKX n → CKVal m) (x₀ : CKX n) : CKForcingInput n m :=
  Prod.mk x₀ (Prod.mk 0 (Prod.mk (u₀ x₀)
    (Prod.mk (ckDataSpatialDerivative u₀ x₀)
      (Prod.mk (ckDataSpatialHessian u₀ x₀)
        (Prod.mk (u₁ x₀) (ckDataSpatialDerivative u₁ x₀))))))

def ckProlongedInitialPoint {n m : ℕ}
    (u₀ u₁ : CKX n → CKVal m) (x₀ : CKX n) : CKFirstOrderInput n m :=
  Prod.mk x₀ (Prod.mk 0 (Prod.mk (ckProlongedInitialData u₀ u₁ x₀)
    (fun i => fderiv ℝ (ckProlongedInitialData u₀ u₁) x₀
      (EuclideanSpace.single i (1 : ℝ)))))

def ckProlongedRhs {n m : ℕ}
    (F : CKForcingInput n m → CKVal m) (z : CKFirstOrderInput n m) : CKState n m :=
  let x := z.1
  let r := z.2.1
  let V := z.2.2.1
  let dV := z.2.2.2
  let hessian : CKHessian n m := fun i j => (dV i).2.1 j
  let mixed : CKSpatial n m := fun i => (dV i).2.2
  let input : CKForcingInput n m :=
    Prod.mk x (Prod.mk r (Prod.mk V.1
      (Prod.mk V.2.1 (Prod.mk hessian (Prod.mk V.2.2 mixed)))))
  Prod.mk V.2.2 (Prod.mk mixed (F input))

def CKOriginalSolution {n m : ℕ}
    (F : CKForcingInput n m → CKVal m) (u₀ u₁ : CKX n → CKVal m)
    (x₀ : CKX n) (ε : ℝ) (u : CKJoint n → CKVal m) : Prop :=
  AnalyticOnNhd ℝ u (Metric.ball ((0 : ℝ), x₀) ε) ∧
    (∀ r x, ((r, x) : CKJoint n) ∈ Metric.ball ((0 : ℝ), x₀) ε →
      ckSecondTimeDerivative u (r, x) =
        F (x, (r, (u (r, x), (ckSpatialDerivative u (r, x),
          (ckSecondSpatialDerivative u (r, x),
            (ckTimeDerivative u (r, x), ckMixedDerivative u (r, x)))))))) ∧
    (∀ x, x ∈ Metric.ball x₀ ε →
      u (0, x) = u₀ x ∧ ckTimeDerivative u (0, x) = u₁ x)

def CKProlongedSolution {n m : ℕ}
    (F : CKForcingInput n m → CKVal m) (u₀ u₁ : CKX n → CKVal m)
    (x₀ : CKX n) (ε : ℝ) (V : CKJoint n → CKState n m) : Prop :=
  AnalyticOnNhd ℝ V (Metric.ball ((0 : ℝ), x₀) ε) ∧
    (∀ r x, ((r, x) : CKJoint n) ∈ Metric.ball ((0 : ℝ), x₀) ε →
      fderiv ℝ V (r, x) ckTimeDirection =
        ckProlongedRhs F (x, (r, (V (r, x),
          fun i => fderiv ℝ V (r, x) (ckSpaceDirection i))))) ∧
    (∀ x, x ∈ Metric.ball x₀ ε → V (0, x) = ckProlongedInitialData u₀ u₁ x)

/-- The actual prolonged initial state is analytic, using the accepted analytic spatial-jet
provider with the identical original Euclidean directions. Source: Gantumur, Corollary 20. -/
theorem ckProlongedInitialData_analyticAt {n m : ℕ}
    (u₀ u₁ : CKX n → CKVal m) (x₀ : CKX n)
    (hu₀ : AnalyticAt ℝ u₀ x₀) (hu₁ : AnalyticAt ℝ u₁ x₀) :
    AnalyticAt ℝ (ckProlongedInitialData u₀ u₁) x₀ := by
  exact hu₀.prod ((collarCKInitialSpatialJet_analyticAt u₀ x₀ hu₀).prod hu₁)

/-- Differentiate the actual prolonged initial tuple in an original spatial direction.
Source: Gantumur, Corollary 20. Native product and finite-function derivative rules give
exactly the original first and second spatial jets; no initial compatibility is assumed. -/
theorem ckProlongedInitialData_fderiv {n m : ℕ}
    (u₀ u₁ : CKX n → CKVal m) (x₀ : CKX n)
    (hu₀ : AnalyticAt ℝ u₀ x₀) (hu₁ : AnalyticAt ℝ u₁ x₀) (i : Fin n) :
    fderiv ℝ (ckProlongedInitialData u₀ u₁) x₀ (EuclideanSpace.single i 1) =
      (ckDataSpatialDerivative u₀ x₀ i,
        (ckDataSpatialHessian u₀ x₀ i, ckDataSpatialDerivative u₁ x₀ i)) := by
  have hd (j : Fin n) : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ u₀ y (EuclideanSpace.single j 1)) x₀ :=
    (((ContinuousLinearMap.apply ℝ (CKVal m) (EuclideanSpace.single j 1 : CKX n)).analyticAt _).comp
      hu₀.fderiv).differentiableAt
  have h := hu₀.differentiableAt.hasFDerivAt.prodMk
    ((hasFDerivAt_pi.mpr (fun j ↦ (hd j).hasFDerivAt)).prodMk
      hu₁.differentiableAt.hasFDerivAt)
  rw [show fderiv ℝ (ckProlongedInitialData u₀ u₁) x₀ = _ from h.fderiv]
  rfl

/-- The original second-order forcing gives an analytic first-order prolonged RHS at the
same actual initial jet. Source: Gantumur, Corollary 20. Its argument rearrangement and the
first two output blocks are genuine finite-dimensional linear maps. The initial derivative
identity identifies the forcing input with the original jet before composing its analytic germ. -/
theorem ckProlongedRhs_analyticAt {n m : ℕ}
    (F : CKForcingInput n m → CKVal m)
    (u₀ u₁ : CKX n → CKVal m) (x₀ : CKX n)
    (hF : AnalyticAt ℝ F (ckForcingInitialPoint u₀ u₁ x₀))
    (hu₀ : AnalyticAt ℝ u₀ x₀) (hu₁ : AnalyticAt ℝ u₁ x₀) :
    AnalyticAt ℝ (ckProlongedRhs F) (ckProlongedInitialPoint u₀ u₁ x₀) := by
  let I : CKFirstOrderInput n m →ₗ[ℝ] CKForcingInput n m :=
    { toFun := fun z ↦ (z.1, (z.2.1, (z.2.2.1.1, (z.2.2.1.2.1,
        ((fun i j ↦ (z.2.2.2 i).2.1 j), (z.2.2.1.2.2, fun i ↦ (z.2.2.2 i).2.2))))))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let L : CKFirstOrderInput n m →ₗ[ℝ] CKVal m :=
    { toFun := fun z ↦ z.2.2.1.2.2
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let P : CKFirstOrderInput n m →ₗ[ℝ] CKSpatial n m :=
    { toFun := fun z i ↦ (z.2.2.2 i).2.2
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hi : I (ckProlongedInitialPoint u₀ u₁ x₀) = ckForcingInitialPoint u₀ u₁ x₀ := by
    dsimp [I, ckProlongedInitialPoint, ckForcingInitialPoint]
    simp_rw [ckProlongedInitialData_fderiv u₀ u₁ x₀ hu₀ hu₁]
    rfl
  exact (L.toContinuousLinearMap.analyticAt _).prod
    ((P.toContinuousLinearMap.analyticAt _).prod
      (hF.comp_of_eq (I.toContinuousLinearMap.analyticAt _) hi))

/-- Analyticity commutes the actual time and spatial derivatives of the original unknown.
Source: Gantumur, Corollary 20 compatibility equation. Reuse native symmetry of the second
Fréchet derivative, and native evaluation of a derivative at a fixed direction. -/
theorem ckSpatial_time_commute {n m : ℕ} (u : CKJoint n → CKVal m) (z : CKJoint n)
    (hu : AnalyticAt ℝ u z) (i : Fin n) :
    fderiv ℝ (fun y ↦ ckSpatialDerivative u y i) z ckTimeDirection =
      ckMixedDerivative u z i := by
  have hsymm := hu.contDiffAt.isSymmSndFDerivAt_of_omega
  unfold ckSpatialDerivative ckMixedDerivative ckTimeDerivative
  rw [fderiv_clm_apply hu.fderiv.differentiableAt (differentiableAt_const _),
    fderiv_clm_apply hu.fderiv.differentiableAt (differentiableAt_const _)]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using hsymm ckTimeDirection (ckSpaceDirection i)

/-- An analytic function with actual zero time derivative on the common product ball is
constant along each normal segment. Source: Gantumur, Corollary 20. Product distance keeps
the entire normal interval in the ball, and the native vector-valued mean value theorem
identifies the value with its initial trace; no compatibility conclusion is assumed. -/
theorem ckTimeDerivative_zero_on_ball {n m : ℕ}
    (H : CKJoint n → CKVal m) (x₀ : CKX n) (ε : ℝ) (hε : 0 < ε)
    (hH : AnalyticOnNhd ℝ H (Metric.ball ((0 : ℝ), x₀) ε))
    (hzero : ∀ z ∈ Metric.ball ((0 : ℝ), x₀) ε, ckTimeDerivative H z = 0)
    (r : ℝ) (x : CKX n) (hz : (r, x) ∈ Metric.ball ((0 : ℝ), x₀) ε) :
    H (r, x) = H (0, x) := by
  have hdist := hz
  simp only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hdist
  have hpoint (t : ℝ) (ht : t ∈ Metric.ball 0 ε) :
      (t, x) ∈ Metric.ball ((0 : ℝ), x₀) ε := by
    simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using And.intro ht hdist.2
  have hd (t : ℝ) (ht : t ∈ Metric.ball 0 ε) : HasDerivAt (fun s ↦ H (s, x)) 0 t := by
    have hline : HasDerivAt (fun s : ℝ ↦ (s, x)) ((1, 0) : CKJoint n) t :=
      HasDerivAt.prodMk (hasDerivAt_id t) (hasDerivAt_const t x)
    have h := (hH (t, x) (hpoint t ht)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hline
    change HasDerivAt (fun s ↦ H (s, x)) (ckTimeDerivative H (t, x)) t at h
    rw [hzero (t, x) (hpoint t ht)] at h
    exact h
  exact Metric.isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball (0 : ℝ) ε).isPreconnected
    (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hd t ht).deriv) hdist.1 (Metric.mem_ball_self hε)

/-- Equality of the actual initial traces gives equality of their actual spatial jets.
Source: Gantumur, Corollary 20. Initial equality on an open spatial ball is a germ equality;
differentiate it and compose the unknown with the genuine zero-time slice. -/
theorem ckSpatialDerivative_initial {n m : ℕ}
    (u : CKJoint n → CKVal m) (u₀ : CKX n → CKVal m) (x₀ : CKX n) (ε : ℝ)
    (hu : AnalyticOnNhd ℝ u (Metric.ball ((0 : ℝ), x₀) ε))
    (htrace : ∀ y ∈ Metric.ball x₀ ε, u (0, y) = u₀ y)
    (x : CKX n) (hx : x ∈ Metric.ball x₀ ε) :
    ckSpatialDerivative u (0, x) = ckDataSpatialDerivative u₀ x := by
  have hz : ((0 : ℝ), x) ∈ Metric.ball ((0 : ℝ), x₀) ε := by
    simpa only [Metric.mem_ball, Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using hx
  have hg : (fun y : CKX n ↦ u (0, y)) =ᶠ[𝓝 x] u₀ := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact htrace y hy
  have hd := (hu (0, x) hz).differentiableAt.hasFDerivAt.comp x
    ((hasFDerivAt_const (0 : ℝ) x).prodMk (hasFDerivAt_id x))
  change HasFDerivAt (fun y : CKX n ↦ u (0, y)) _ x at hd
  funext i
  change fderiv ℝ u (0, x) (ckSpaceDirection i) =
    fderiv ℝ u₀ x (EuclideanSpace.single i 1)
  rw [← hg.fderiv_eq, hd.fderiv]
  rfl

/-- The genuine prolonged state consists of the unknown and all actual first derivatives.
Source: Gantumur, Corollary 20. This uses precisely the original frozen product state. -/
def ckProlongation {n m : ℕ} (u : CKJoint n → CKVal m) (z : CKJoint n) : CKState n m :=
  (u z, (ckSpatialDerivative u z, ckTimeDerivative u z))

/-- Actual analytic derivatives assemble an analytic prolongation at the same point.
Source: Gantumur, Corollary 20; use native analytic Fréchet derivative and bounded evaluation. -/
theorem ckProlongation_analyticAt {n m : ℕ} (u : CKJoint n → CKVal m) (z : CKJoint n)
    (hu : AnalyticAt ℝ u z) : AnalyticAt ℝ (ckProlongation u) z := by
  have hsp : AnalyticAt ℝ (ckSpatialDerivative u) z := by
    apply AnalyticAt.pi
    intro i
    exact ((ContinuousLinearMap.apply ℝ (CKVal m) (ckSpaceDirection i)).analyticAt _).comp
      hu.fderiv
  exact hu.prod (hsp.prod
    (((ContinuousLinearMap.apply ℝ (CKVal m) ckTimeDirection).analyticAt _).comp hu.fderiv))

/-- Differentiate every genuine block of the prolonged state, without replacing actual jets
by independent formal variables. Source: Gantumur, Corollary 20. -/
theorem ckProlongation_fderiv {n m : ℕ} (u : CKJoint n → CKVal m) (z v : CKJoint n)
    (hu : AnalyticAt ℝ u z) :
    fderiv ℝ (ckProlongation u) z v =
      (fderiv ℝ u z v, ((fun i ↦ fderiv ℝ (fun y ↦ ckSpatialDerivative u y i) z v),
        fderiv ℝ (ckTimeDerivative u) z v)) := by
  have hsp (i : Fin n) : DifferentiableAt ℝ (fun y ↦ ckSpatialDerivative u y i) z :=
    (((ContinuousLinearMap.apply ℝ (CKVal m) (ckSpaceDirection i)).analyticAt _).comp
      hu.fderiv).differentiableAt
  have ht : DifferentiableAt ℝ (ckTimeDerivative u) z :=
    (((ContinuousLinearMap.apply ℝ (CKVal m) ckTimeDirection).analyticAt _).comp
      hu.fderiv).differentiableAt
  have h := hu.differentiableAt.hasFDerivAt.prodMk
    ((hasFDerivAt_pi.mpr (fun i ↦ (hsp i).hasFDerivAt)).prodMk ht.hasFDerivAt)
  rw [show fderiv ℝ (ckProlongation u) z = _ from h.fderiv]
  rfl

/-- Every genuine original analytic second-order solution prolongs to a solution of the
fixed first-order system on the same ball. Source: Gantumur, Corollary 20. Differentiate the
actual state tuple, commute actual mixed derivatives, and differentiate the actual initial
trace. The last evolution equation is exactly the original PDE. -/
theorem ckOriginalSolution_prolongs {n m : ℕ}
    (F : CKForcingInput n m → CKVal m) (u₀ u₁ : CKX n → CKVal m)
    (x₀ : CKX n) (ε : ℝ) (u : CKJoint n → CKVal m)
    (hu : CKOriginalSolution F u₀ u₁ x₀ ε u) :
    CKProlongedSolution F u₀ u₁ x₀ ε (ckProlongation u) := by
  rcases hu with ⟨ha, hpde, hinit⟩
  refine ⟨fun z hz ↦ ckProlongation_analyticAt u z (ha z hz), ?_, ?_⟩
  · intro r x hz
    have h := ha (r, x) hz
    rw [ckProlongation_fderiv u (r, x) ckTimeDirection h]
    simp_rw [ckProlongation_fderiv u (r, x) _ h]
    apply Prod.ext
    · rfl
    apply Prod.ext
    · funext i
      exact ckSpatial_time_commute u (r, x) h i
    · exact hpde r x hz
  · intro x hx
    have hsp := ckSpatialDerivative_initial u u₀ x₀ ε ha
      (fun y hy ↦ (hinit y hy).1) x hx
    change (u (0, x), (ckSpatialDerivative u (0, x), ckTimeDerivative u (0, x))) = _
    rw [(hinit x hx).1, (hinit x hx).2, hsp]
    rfl

/-- Every actual prolonged solution has the genuine spatial and normal jets of its first
component. Source: Gantumur, Corollary 20. The first evolution equation gives the normal jet.
For each spatial direction, the difference between the introduced jet and the actual spatial
derivative has zero normal derivative, by mixed-derivative symmetry and the other evolution
equations. Its initial trace is zero. Actual normal constancy in the common ball proves the
spatial identity everywhere; agreement of the initial jets alone is never used as a substitute. -/
theorem ckProlongedSolution_compatible {n m : ℕ}
    (F : CKForcingInput n m → CKVal m) (u₀ u₁ : CKX n → CKVal m)
    (x₀ : CKX n) (ε : ℝ) (hε : 0 < ε) (V : CKJoint n → CKState n m)
    (hV : CKProlongedSolution F u₀ u₁ x₀ ε V) :
    ∀ r x, (r, x) ∈ Metric.ball ((0 : ℝ), x₀) ε →
      (V (r, x)).2.1 = ckSpatialDerivative (fun z ↦ (V z).1) (r, x) ∧
      (V (r, x)).2.2 = ckTimeDerivative (fun z ↦ (V z).1) (r, x) := by
  rcases hV with ⟨ha, hpde, hinit⟩
  let u : CKJoint n → CKVal m := fun z ↦ (V z).1
  let v : CKJoint n → CKVal m := fun z ↦ (V z).2.2
  let w : CKJoint n → CKSpatial n m := fun z ↦ (V z).2.1
  have hau (z) (hz : z ∈ Metric.ball ((0 : ℝ), x₀) ε) : AnalyticAt ℝ u z :=
    analyticAt_fst.comp (ha z hz)
  have hav (z) (hz : z ∈ Metric.ball ((0 : ℝ), x₀) ε) : AnalyticAt ℝ v z :=
    analyticAt_snd.comp (analyticAt_snd.comp (ha z hz))
  have haw (z) (hz : z ∈ Metric.ball ((0 : ℝ), x₀) ε) (i : Fin n) :
      AnalyticAt ℝ (fun y ↦ w y i) z :=
    ((ContinuousLinearMap.proj i : CKSpatial n m →L[ℝ] CKVal m).analyticAt _).comp
      (analyticAt_fst.comp (analyticAt_snd.comp (ha z hz)))
  have hdu (z) (hz : z ∈ Metric.ball ((0 : ℝ), x₀) ε) (a : CKJoint n) :
      fderiv ℝ u z a = (fderiv ℝ V z a).1 :=
    congrArg (fun L : CKJoint n →L[ℝ] CKVal m ↦ L a)
      (ha z hz).differentiableAt.hasFDerivAt.fst.fderiv
  have hdv (z) (hz : z ∈ Metric.ball ((0 : ℝ), x₀) ε) (a : CKJoint n) :
      fderiv ℝ v z a = (fderiv ℝ V z a).2.2 :=
    congrArg (fun L : CKJoint n →L[ℝ] CKVal m ↦ L a)
      (ha z hz).differentiableAt.hasFDerivAt.snd.snd.fderiv
  have hdw (z) (hz : z ∈ Metric.ball ((0 : ℝ), x₀) ε) (a : CKJoint n) (i : Fin n) :
      fderiv ℝ (fun y ↦ w y i) z a = (fderiv ℝ V z a).2.1 i :=
    congrArg (fun L : CKJoint n →L[ℝ] CKVal m ↦ L a)
      ((hasFDerivAt_pi'.mp (ha z hz).differentiableAt.hasFDerivAt.snd.fst) i).fderiv
  have ht (z) (hz : z ∈ Metric.ball ((0 : ℝ), x₀) ε) : ckTimeDerivative u z = v z := by
    calc
      ckTimeDerivative u z = (fderiv ℝ V z ckTimeDirection).1 := hdu z hz _
      _ = v z := congrArg Prod.fst (hpde z.1 z.2 hz)
  have htg (z) (hz : z ∈ Metric.ball ((0 : ℝ), x₀) ε) :
      ckTimeDerivative u =ᶠ[𝓝 z] v := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact ht y hy
  have hdtw (z) (hz : z ∈ Metric.ball ((0 : ℝ), x₀) ε) (i : Fin n) :
      fderiv ℝ (fun y ↦ w y i) z ckTimeDirection =
        fderiv ℝ v z (ckSpaceDirection i) := by
    rw [hdw z hz, hdv z hz]
    exact congrArg (fun a : CKState n m ↦ a.2.1 i) (hpde z.1 z.2 hz)
  have hspinit (x) (hx : x ∈ Metric.ball x₀ ε) :
      ckSpatialDerivative u (0, x) = ckDataSpatialDerivative u₀ x :=
    ckSpatialDerivative_initial u u₀ x₀ ε hau
      (fun y hy ↦ congrArg Prod.fst (hinit y hy)) x hx
  have hsp (i : Fin n) : ∀ r x, (r, x) ∈ Metric.ball ((0 : ℝ), x₀) ε →
      w (r, x) i = ckSpatialDerivative u (r, x) i := by
    let D : CKJoint n → CKVal m := fun z ↦ w z i - ckSpatialDerivative u z i
    have hDa : AnalyticOnNhd ℝ D (Metric.ball ((0 : ℝ), x₀) ε) := by
      intro z hz
      exact (haw z hz i).sub
        (((ContinuousLinearMap.apply ℝ (CKVal m) (ckSpaceDirection i)).analyticAt _).comp
          (hau z hz).fderiv)
    have hDz (z) (hz : z ∈ Metric.ball ((0 : ℝ), x₀) ε) : ckTimeDerivative D z = 0 := by
      change fderiv ℝ (fun y ↦ w y i - ckSpatialDerivative u y i) z ckTimeDirection = 0
      have hspdif : DifferentiableAt ℝ (fun y ↦ ckSpatialDerivative u y i) z :=
        (((ContinuousLinearMap.apply ℝ (CKVal m) (ckSpaceDirection i)).analyticAt _).comp
          (hau z hz).fderiv).differentiableAt
      rw [fderiv_fun_sub (haw z hz i).differentiableAt hspdif,
        sub_apply,
        ckSpatial_time_commute u z (hau z hz) i, hdtw z hz i]
      change fderiv ℝ v z (ckSpaceDirection i) -
        fderiv ℝ (ckTimeDerivative u) z (ckSpaceDirection i) = 0
      rw [(htg z hz).fderiv_eq, sub_self]
    intro r x hz
    have hx : x ∈ Metric.ball x₀ ε := by
      have h := hz
      simp only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at h
      exact h.2
    have hD0 : D (0, x) = 0 := by
      have hi := congrArg (fun a : CKState n m ↦ a.2.1 i) (hinit x hx)
      change w (0, x) i - ckSpatialDerivative u (0, x) i = 0
      rw [hspinit x hx]
      exact sub_eq_zero.mpr hi
    have hconst := ckTimeDerivative_zero_on_ball D x₀ ε hε hDa hDz r x hz
    exact sub_eq_zero.mp (hconst.trans hD0)
  intro r x hz
  exact ⟨funext (fun i ↦ hsp i r x hz), (ht (r, x) hz).symm⟩

/-- The first component of every genuine prolonged solution solves the original equation
on the same ball. Source: Gantumur, Corollary 20. Established jet compatibility identifies
the entire state with the actual prolongation throughout the open ball, hence identifies its
actual derivatives by germ equality. Projecting the last evolution equation gives the original
second-order PDE with the exact original spatial Hessian and mixed derivatives. -/
theorem ckProlongedSolution_original {n m : ℕ}
    (F : CKForcingInput n m → CKVal m) (u₀ u₁ : CKX n → CKVal m)
    (x₀ : CKX n) (ε : ℝ) (hε : 0 < ε) (V : CKJoint n → CKState n m)
    (hV : CKProlongedSolution F u₀ u₁ x₀ ε V) :
    CKOriginalSolution F u₀ u₁ x₀ ε (fun z ↦ (V z).1) := by
  have hc := ckProlongedSolution_compatible F u₀ u₁ x₀ ε hε V hV
  rcases hV with ⟨ha, hpde, hinit⟩
  let u : CKJoint n → CKVal m := fun z ↦ (V z).1
  have hau (z) (hz : z ∈ Metric.ball ((0 : ℝ), x₀) ε) : AnalyticAt ℝ u z :=
    analyticAt_fst.comp (ha z hz)
  have heq (z) (hz : z ∈ Metric.ball ((0 : ℝ), x₀) ε) : V z = ckProlongation u z :=
    Prod.ext rfl (Prod.ext (hc z.1 z.2 hz).1 (hc z.1 z.2 hz).2)
  refine ⟨hau, ?_, ?_⟩
  · intro r x hz
    have hg : V =ᶠ[𝓝 (r, x)] ckProlongation u := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
      exact heq y hy
    have h := hpde r x hz
    simp only [heq (r, x) hz, hg.fderiv_eq] at h
    simp_rw [ckProlongation_fderiv u (r, x) _ (hau (r, x) hz)] at h
    exact congrArg (fun a : CKState n m ↦ a.2.2) h
  · intro x hx
    have hz : ((0 : ℝ), x) ∈ Metric.ball ((0 : ℝ), x₀) ε := by
      simpa only [Metric.mem_ball, Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using hx
    exact ⟨congrArg Prod.fst (hinit x hx),
      (hc 0 x hz).2.symm.trans (congrArg (fun a : CKState n m ↦ a.2.2) (hinit x hx))⟩

/-- Prolongation preserves and reflects genuine germs. Source: Gantumur, Corollary 20,
uniqueness under prolongation. Native germ equality preserves the actual Fréchet derivative;
the first component reflects equality. This interface transfers the sole first-order CK
uniqueness theorem to the original unknown without a second analytic uniqueness proof. -/
theorem ckProlongation_germ_iff {n m : ℕ} (u v : CKJoint n → CKVal m) (z : CKJoint n) :
    (ckProlongation u =ᶠ[𝓝 z] ckProlongation v) ↔ u =ᶠ[𝓝 z] v := by
  constructor
  · intro h
    exact h.mono (fun _ hy ↦ congrArg Prod.fst hy)
  · intro h
    have hd : fderiv ℝ u =ᶠ[𝓝 z] fderiv ℝ v := h.fderiv
    filter_upwards [h, hd] with y hy hdy
    have hsp : ckSpatialDerivative u y = ckSpatialDerivative v y := by
      funext i
      exact congrArg (fun L : CKJoint n →L[ℝ] CKVal m ↦ L (ckSpaceDirection i)) hdy
    simp only [ckProlongation, ckTimeDerivative, hy, hdy, hsp]

/-- The order-two Cauchy system is equivalent locally to its analytic first-order prolongation.

Proof: use the state `V=(u,u_x,u_r)`. Its normal derivative is the tuple whose entries are
`u_r`, `∂_x u_r`, and `F(x,r,u,u_x,u_xx,u_r,u_xr)`. This is exactly `ckProlongedRhs`; since it is
formed from coordinate projections and the analytic map `F`, its right side is analytic at the
initial prolonged jet. The initial state is `(u₀,∂_x u₀,u₁)`, which is analytic.

If `u` solves the original equation, its analytic spatial and normal derivatives are analytic on
any smaller ball; differentiating the defining tuple gives the prolonged system and its initial
trace. Conversely, let `V` solve the prolonged system with that initial trace. The first component
of its evolution equation gives `∂_r V₀=Vᵣ`; its spatial components give
`∂_r Vⱼ=∂_xⱼVᵣ`. Analyticity permits commutation of the mixed derivatives, so
`∂_r(Vⱼ−∂_xⱼV₀)=0`. The initial trace makes this difference zero at `r=0`; integrating along the
normal segment in the common ball yields `Vⱼ=∂_xⱼV₀` throughout a smaller ball. The first
component equation already gives `Vᵣ=∂_rV₀`. Substituting both identities into the last component
of the system proves that `V₀` solves the original equation with the given Cauchy data. These
constructions give both implications of local solution equivalence.

This is the finite-dimensional order-two prolongation in Corollary 20 of Gantumur. The
Cauchy–Kovalevskaya existence theorem is a separate dependency; this theorem only identifies the
systems and their solutions.
-/
theorem collarCauchyKovalevskayaJetReduction
    {n m : ℕ}
    (F : CKForcingInput n m → CKVal m)
    (u₀ u₁ : CKX n → CKVal m) (x₀ : CKX n)
    (hF : AnalyticAt ℝ F (ckForcingInitialPoint u₀ u₁ x₀))
    (hu₀ : AnalyticAt ℝ u₀ x₀) (hu₁ : AnalyticAt ℝ u₁ x₀) :
    AnalyticAt ℝ (ckProlongedRhs F) (ckProlongedInitialPoint u₀ u₁ x₀) ∧
    (((∃ ε, 0 < ε ∧ ∃ u, CKOriginalSolution F u₀ u₁ x₀ ε u) ↔
      (∃ ε, 0 < ε ∧ ∃ V, CKProlongedSolution F u₀ u₁ x₀ ε V))) ∧
    (∀ ε, 0 < ε → ∀ V, CKProlongedSolution F u₀ u₁ x₀ ε V →
      ∃ δ, 0 < δ ∧ δ ≤ ε ∧
        CKOriginalSolution F u₀ u₁ x₀ δ (fun z => (V z).1) ∧
        (∀ r x, ((r, x) : CKJoint n) ∈ Metric.ball ((0 : ℝ), x₀) δ →
          (V (r, x)).2.1 =
            ckSpatialDerivative (fun z => (V z).1) (r, x) ∧
          (V (r, x)).2.2 = ckTimeDerivative (fun z => (V z).1) (r, x))) := by
  refine ⟨ckProlongedRhs_analyticAt F u₀ u₁ x₀ hF hu₀ hu₁, ?_, ?_⟩
  · constructor
    · rintro ⟨ε, hε, u, hu⟩
      exact ⟨ε, hε, ckProlongation u, ckOriginalSolution_prolongs F u₀ u₁ x₀ ε u hu⟩
    · rintro ⟨ε, hε, V, hV⟩
      exact ⟨ε, hε, (fun z ↦ (V z).1), ckProlongedSolution_original F u₀ u₁ x₀ ε hε V hV⟩
  · intro ε hε V hV
    exact ⟨ε, hε, le_rfl, ckProlongedSolution_original F u₀ u₁ x₀ ε hε V hV,
      ckProlongedSolution_compatible F u₀ u₁ x₀ ε hε V hV⟩

end

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.ckProlongedInitialData_analyticAt
#print axioms GlobalEmbedding.Paper.ckProlongedInitialData_fderiv
#print axioms GlobalEmbedding.Paper.ckProlongedRhs_analyticAt
#print axioms GlobalEmbedding.Paper.ckSpatial_time_commute

#print axioms GlobalEmbedding.Paper.ckTimeDerivative_zero_on_ball
#print axioms GlobalEmbedding.Paper.ckSpatialDerivative_initial
#print axioms GlobalEmbedding.Paper.ckProlongation_analyticAt
#print axioms GlobalEmbedding.Paper.ckProlongation_fderiv
#print axioms GlobalEmbedding.Paper.ckOriginalSolution_prolongs

#print axioms GlobalEmbedding.Paper.ckProlongedSolution_compatible

#print axioms GlobalEmbedding.Paper.ckProlongedSolution_original
#print axioms GlobalEmbedding.Paper.ckProlongation_germ_iff
#print axioms GlobalEmbedding.Paper.collarCauchyKovalevskayaJetReduction

#print axioms GlobalEmbedding.Paper.CKX
#print axioms GlobalEmbedding.Paper.CKVal
#print axioms GlobalEmbedding.Paper.CKSpatial
#print axioms GlobalEmbedding.Paper.CKHessian
#print axioms GlobalEmbedding.Paper.CKState
#print axioms GlobalEmbedding.Paper.CKForcingInput
#print axioms GlobalEmbedding.Paper.CKFirstOrderInput
#print axioms GlobalEmbedding.Paper.CKJoint
#print axioms GlobalEmbedding.Paper.ckTimeDirection
#print axioms GlobalEmbedding.Paper.ckSpaceDirection
#print axioms GlobalEmbedding.Paper.ckDataSpatialDerivative
#print axioms GlobalEmbedding.Paper.ckDataSpatialHessian
#print axioms GlobalEmbedding.Paper.ckTimeDerivative
#print axioms GlobalEmbedding.Paper.ckSpatialDerivative
#print axioms GlobalEmbedding.Paper.ckSecondTimeDerivative
#print axioms GlobalEmbedding.Paper.ckSecondSpatialDerivative
#print axioms GlobalEmbedding.Paper.ckMixedDerivative
#print axioms GlobalEmbedding.Paper.ckProlongedInitialData
#print axioms GlobalEmbedding.Paper.ckForcingInitialPoint
#print axioms GlobalEmbedding.Paper.ckProlongedInitialPoint
#print axioms GlobalEmbedding.Paper.ckProlongedRhs
#print axioms GlobalEmbedding.Paper.CKOriginalSolution
#print axioms GlobalEmbedding.Paper.CKProlongedSolution
#print axioms GlobalEmbedding.Paper.ckProlongation
