import NormalPolar.PassiveOriginalParameterRaw
import GlobalEmbedding.Paper.BufferedAtlas
import GlobalEmbedding.Offline.BufferedSamplingDomains
import Mathlib.Algebra.Order.Field.Pi

/-! A real initial choice of a prepared finite parameter atlas on the unchanged compact
manifold. Each original chart has three radii: the covering inner ball r/3,
the compact norm domain r/2, and the new restricted target 2r/3. A positive
common buffer is smaller than every r/6. The forward coordinates are the
globally smooth cutoff construction, agreeing with the original coordinates
on the entire new chart source. Thus the actual parameter transition
functions are smooth across every other chart's source boundary. -/

noncomputable section
open Set Function Manifold IsManifold Metric GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {d : ℕ} {P : Type*} [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] [CompactSpace P]

/-- Construction of the original input parameter atlas with global smooth
forward maps and actual compact norm samples. This selects new legal B/Q;
it does not alter an already supplied atlas or its evaluation domain. -/
theorem passiveOriginal_exists_global_forward_prepared_parameter_atlas :
    ∃ B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)),
      IsSmoothBufferedAtlas B ∧
      (∀ i, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d))
        𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ (B.chart i)) ∧
      ∃ Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)),
        (∀ i, IsCompact (Q i) ∧ Q i ⊆ (B.chart i).target ∧
          closure (bufferedSamplingCoordinates B i) ⊆ Q i) ∧
        ∃ BP TP : ℕ → ℝ, (∀ k, 0 ≤ BP k) ∧ (∀ k, 0 ≤ TP k) ∧
          Nonempty (TensorRawCutoffPreparation B BP TP B.supportDegree) := by
  let E := EuclideanSpace ℝ (Fin d)
  have hball (p : P) : ∃ r : ℝ, 0 < r ∧
      closedBall (chartAt E p p) r ⊆ (chartAt E p).target := by
    obtain ⟨r,hr,hs⟩ := Metric.isOpen_iff.mp (chartAt E p).open_target _ (mem_chart_target E p)
    exact ⟨r/2,by positivity,(closedBall_subset_ball (by linarith : r/2<r)).trans hs⟩
  choose radius hpos htarget using hball
  let bump (p : P) : ContDiffBump (chartAt E p p) := {
    rIn := 2*radius p/3
    rOut := radius p
    rIn_pos := by have := hpos p; positivity
    rIn_lt_rOut := by have := hpos p; linarith }
  let e (p : P) := passiveOriginalGlobalParameterChart (chartAt E p) (chartAt E p p)
    (bump p) (htarget p)
  let U (p : P) := (chartAt E p).source ∩
    (chartAt E p) ⁻¹' ball (chartAt E p p) (radius p/3)
  have hU (p : P) : IsOpen (U p) := (chartAt E p).isOpen_inter_preimage isOpen_ball
  have hself (p : P) : p ∈ U p :=
    ⟨mem_chart_source E p,mem_ball_self (by have := hpos p; positivity)⟩
  obtain ⟨centers,hcover⟩ := isCompact_univ.elim_finite_subcover U hU
    (show (univ : Set P) ⊆ ⋃ p, U p from fun p _ => mem_iUnion.mpr ⟨p,hself p⟩)
  obtain ⟨eps,heps,hsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : centers => (0 : ℝ)) (y := fun p : centers => radius p.val/6)
    (fun p => by have := hpos p.val; positivity)
  let c : Fin (Fintype.card centers) → P := fun i => ((Fintype.equivFin centers).symm i).val
  have heq (p x : P) (hx : x ∈ U p) : e p x = chartAt E p x := by
    exact passiveOriginalParameterCutoff_eq (chartAt E p) (chartAt E p p) (bump p) x hx.1
      (ball_subset_closedBall ((ball_subset_ball (by have := hpos p; dsimp [bump]; linarith)) hx.2))
  have hsource (p : P) : U p ⊆ (e p).source := by
    intro x hx
    refine ⟨hx.1,?_⟩
    exact (ball_subset_ball (by have := hpos p; dsimp [bump]; linarith)) hx.2
  let Q (i : Fin (Fintype.card centers)) := closedBall (chartAt E (c i) (c i)) (radius (c i)/2)
  have hQtarget (i : Fin (Fintype.card centers)) : Q i ⊆ (e (c i)).target := by
    exact closedBall_subset_ball (by have := hpos (c i); dsimp [bump]; linarith)
  have hbuffer (i : Fin (Fintype.card centers)) (x : P) (hx : x ∈ U (c i)) :
      ball (e (c i) x) eps ⊆ Q i := by
    intro y hy
    have heps' : eps < radius (c i)/6 := by
      simpa only [zero_add] using hsmall ((Fintype.equivFin centers).symm i)
    rw [heq (c i) x hx] at hy
    have hxy : dist y (chartAt E (c i) x) < eps := hy
    have hxc : dist (chartAt E (c i) x) (chartAt E (c i) (c i)) < radius (c i)/3 := hx.2
    have htri := dist_triangle y (chartAt E (c i) x) (chartAt E (c i) (c i))
    change dist y (chartAt E (c i) (c i)) ≤ radius (c i)/2
    linarith
  let B : BufferedAtlas P E := {
    count := Fintype.card centers
    chart := fun i => e (c i)
    inner := fun i => U (c i)
    inner_open := fun i => hU (c i)
    inner_subset := fun i => hsource (c i)
    cover := by
      intro x
      obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
      refine ⟨(Fintype.equivFin centers) ⟨p,hp⟩,?_⟩
      simpa only [c,Equiv.symm_apply_apply] using hx
    buffer := eps
    buffer_pos := heps
    buffered := fun i x hx => (hbuffer i x hx).trans (hQtarget i)
    support := fun i => U (c i) }
  refine ⟨B,⟨?_,fun i => hsource (c i)⟩,?_,Q,?_,?_⟩
  · intro i
    exact passiveOriginalGlobalParameterChart_mem_maximalAtlas (chartAt E (c i))
      (chart_mem_maximalAtlas (c i)) (chartAt E (c i) (c i)) (bump (c i)) (htarget (c i))
  · intro i
    exact passiveOriginalGlobalParameterChart_smooth (chartAt E (c i))
      (chart_mem_maximalAtlas (c i)) (chartAt E (c i) (c i)) (bump (c i)) (htarget (c i))
  · intro i
    refine ⟨isCompact_closedBall _ _,hQtarget i,?_⟩
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    obtain ⟨z,hz⟩ := mem_iUnion.mp hy
    obtain ⟨hzInner,hyball⟩ := mem_iUnion.mp hz
    have h := hbuffer i ((B.chart i).symm z) hzInner.2
    rw [(B.chart i).right_inv hzInner.1] at h
    exact h hyball

  · apply passiveOriginal_parameter_raw_of_inverse_collars B
      (fun i => passiveOriginalGlobalParameterChart_smooth (chartAt E (c i))
        (chart_mem_maximalAtlas (c i)) (chartAt E (c i) (c i)) (bump (c i)) (htarget (c i)))
      (fun _ => Subset.rfl) (fun i => chartAt E (c i))
      (fun i => chart_mem_maximalAtlas (c i)) (fun _ => rfl)
      (fun i => closedBall (chartAt E (c i) (c i)) (radius (c i)))
      (fun i => isCompact_closedBall _ _) ?_ (fun i => htarget (c i))
    intro i
    exact ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by have := hpos (c i); dsimp [bump]; linarith))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_exists_global_forward_prepared_parameter_atlas
