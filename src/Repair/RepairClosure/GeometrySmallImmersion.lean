import RepairClosure.GeometrySmallImmersionNorm
import RepairClosure.GeometrySmallImmersionStatement
import GlobalEmbedding.Offline.ImmersionRescaling

/-!
# The same repaired map gives a small exact immersion after inverse scaling

The geometric rescaling identities are reused from `ImmersionRescaling`.
The new work here connects the literal original repair C2 bound to an
actual uniform Euclidean value bound, using the original chart covers.
The scaled map is explicitly `T⁻¹ • Fstar`, and the strict supremum bound
is valid also for empty and disconnected sources.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Bundle
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Continuation.RepairClosure
open OriginalIntegration

variable {b : OriginalRepairGeometryBudget} {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)

private local instance geometrySmallProductChart : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
private local instance geometrySmallProductManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

/-- The small-immersion conclusion for an actual joint map.  In particular,
the last field is a strict uniform supremum, not merely individual strict
pointwise bounds without a common smaller radius. -/
structure GeometrySmallImmersionConclusion
    (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (r : ℝ) (f : P × M → V) : Prop where
  joint_smooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,V) ∞ f
  slice_smooth : ∀ p, ContMDiff 𝓘(ℝ,Es) 𝓘(ℝ,V) ∞ (fun x => f (p,x))
  exact_metric : ∀ p, inducedMetric (I := 𝓘(ℝ,Es)) (fun x => f (p,x)) = metric p
  immersion : ∀ p x, Function.Injective
    (mfderiv 𝓘(ℝ,Es) 𝓘(ℝ,V) (fun y => f (p,y)) x)
  phase_regular : ∀ p, PhaseRegular (fun x => f (p,x)) (slice_smooth p)
  image_bound : (⨆ z : P × M, ENNReal.ofReal ‖f z‖) < ENNReal.ofReal r

/-- The full original repair output, including its actual C2 estimate,
supplies a uniform value bound for the same Fstar. -/
theorem geometry_repair_value_bound
    (g : OriginalRepairGeometry b (m+1) d M P)
    (F0 Fstar : P × M → V)
    (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (rho t0 value : ℝ) (hrho : 0 < rho)
    (G u : ℕ → P × M → V) (stage : ℕ → ℕ)
    (out : OriginalRepairConclusion g.atlas g.parameterChart g.Omega g.Q
      F0 metric rho t0 Fstar G u stage)
    (hValue : ∀ z, ‖F0 z‖ ≤ value) :
    ∀ z, ‖Fstar z‖ ≤ value + geometrySmallImmersionValueFactor N * rho := by
  intro z
  have hDifference := geometry_original_map_value_lt g (fun w => Fstar w-F0 w)
    2 rho hrho out.strict_C2 z.1 z.2
  calc
    ‖Fstar z‖ = ‖(Fstar z-F0 z)+F0 z‖ := by rw [sub_add_cancel]
    _ ≤ ‖Fstar z-F0 z‖ + ‖F0 z‖ := norm_add_le _ _
    _ ≤ geometrySmallImmersionValueFactor N * rho + value :=
      add_le_add hDifference.le (hValue z)
    _ = value + geometrySmallImmersionValueFactor N * rho := add_comm _ _

/-- Inverse scaling of the literal repaired map gives the original exact
metric and native phase regularity, and its image has a strict common
radius. No new repair or phase-regularization hypothesis is supplied. -/
theorem geometry_small_immersion_of_repair
    (g : OriginalRepairGeometry b (m+1) d M P)
    (F0 Fstar : P × M → V)
    (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (rho t0 value T r : ℝ) (hrho : 0 < rho) (hT : 0 < T) (hr : 0 < r)
    (G u : ℕ → P × M → V) (stage : ℕ → ℕ)
    (out : OriginalRepairConclusion g.atlas g.parameterChart g.Omega g.Q
      F0 (fun p x => T^2 • metric p x) rho t0 Fstar G u stage)
    (hValue : ∀ z, ‖F0 z‖ ≤ value)
    (hSmall : value + geometrySmallImmersionValueFactor N * rho < r*T) :
    GeometrySmallImmersionConclusion (d := d) metric r (T⁻¹ • Fstar) := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have hInv : T⁻¹ ≠ 0 := inv_ne_zero hTne
  have hBound := geometry_repair_value_bound g F0 Fstar
    (fun p x => T^2 • metric p x) rho t0 value hrho G u stage out hValue
  refine {
    joint_smooth := contMDiff_const_rescale Fstar out.joint_smooth T⁻¹
    slice_smooth := fun p => contMDiff_const_rescale (fun x => Fstar (p,x))
      (out.slice_smooth p) T⁻¹
    exact_metric := ?_
    immersion := ?_
    phase_regular := ?_
    image_bound := ?_ }
  · intro p
    funext x
    exact inducedMetric_inverse_rescale (fun y => Fstar (p,y)) (out.slice_smooth p)
      (metric p) T hTne (fun y => congrFun (out.exact_metric p) y) x
  · intro p x
    exact (immersion_const_rescale_iff (fun y => Fstar (p,y)) (out.slice_smooth p)
      T⁻¹ hInv x).mpr (out.slice_immersion p x)
  · intro p
    exact (phaseRegular_const_rescale_iff (fun y => Fstar (p,y)) (out.slice_smooth p)
      T⁻¹ hInv).mpr (out.phase_regular p)
  · have hpoint (z : P × M) :
        ‖(T⁻¹ • Fstar) z‖ ≤ (value+geometrySmallImmersionValueFactor N*rho)/T := by
      calc
        ‖(T⁻¹ • Fstar) z‖ = ‖Fstar z‖/T := by
          rw [norm_const_rescale,abs_of_pos (inv_pos.mpr hT),div_eq_mul_inv,mul_comm]
        _ ≤ (value+geometrySmallImmersionValueFactor N*rho)/T :=
          div_le_div_of_nonneg_right (hBound z) hT.le
    exact (iSup_le (fun z => ENNReal.ofReal_le_ofReal (hpoint z))).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hr).mpr ((div_lt_iff₀ hT).mpr hSmall))

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
/-- The supremum conclusion puts every actual image point in the requested
open Euclidean ball. This includes the empty-source case without a choice. -/
theorem GeometrySmallImmersionConclusion.mapsTo_ball
    {metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x)}
    {r : ℝ} {f : P × M → V} (h : GeometrySmallImmersionConclusion (d := d) metric r f)
    (hr : 0 < r) : MapsTo f univ (Metric.ball 0 r) := by
  intro z _
  rw [Metric.mem_ball,dist_zero_right]
  exact (ENNReal.ofReal_lt_ofReal_iff hr).mp ((le_iSup (fun z : P × M =>
    ENNReal.ofReal ‖f z‖) z).trans_lt h.image_bound)

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
/-- Any supplied parameter point gives a literal small exact immersion of
the original source. Its image supremum is bounded by the one joint bound. -/
theorem GeometrySmallImmersionConclusion.slice
    {metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x)}
    {r : ℝ} {f : P × M → V}
    (h : GeometrySmallImmersionConclusion (d := d) metric r f) (p : P) :
    SmallExactImmersionConclusion (metric p) r (fun x => f (p,x)) := by
  refine { smooth := h.slice_smooth p
           exact_metric := h.exact_metric p
           immersion := h.immersion p
           phase_regular := h.phase_regular p
           image_bound := ?_ }
  exact (iSup_le (fun x => le_iSup (fun z : P × M => ENNReal.ofReal ‖f z‖) (p,x))).trans_lt
    h.image_bound

end GlobalEmbedding.Continuation.RepairClosure

#print axioms GlobalEmbedding.Continuation.RepairClosure.geometry_repair_value_bound
#print axioms GlobalEmbedding.Continuation.RepairClosure.geometry_small_immersion_of_repair
#print axioms GlobalEmbedding.Continuation.RepairClosure.GeometrySmallImmersionConclusion.mapsTo_ball
#print axioms GlobalEmbedding.Continuation.RepairClosure.GeometrySmallImmersionConclusion.slice
