import Smoothing.Round4ReboundSampleMeta
import Probes.Round3ParameterOriginalMeanPreparation
/-! The actual rebound normal/physical mean preparation consumes the proved
reference Meta profile. The same native fields, slices, transverse reserve
and family identity are retained; only the numerical sample Meta argument
is replaced. This record is the literal input to the original raw observer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P A : Type*} [TopologicalSpace M] [TopologicalSpace P] [Fintype A]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × Es
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,Es)

def round4_actual_rebound_native_mean_preparation
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (g0 : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Ref.primaryCount) (Β := A) (fun p x => Ref.F (p,x)))
    (R : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry Ref g0 R)
    (Forward Inverse Meta : ℕ → ℝ)
    (hProfiles : Round3ParameterOriginalChartProfiles Ref g0 Forward Inverse Meta)
    (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (V : Set P) (normal : Fin Ref.primaryCount → P × M → Ey)
    (domain : Fin Ref.primaryCount → Set (P × M))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm})
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Ref.primaryCount) (Β := A) (fun p x => F (p,x)))
    (hCutoff : g.cutoff = Ref.cutoff)
    (hEta : g.eta = fun nu => round3FixedCarrierCutoff (g0.eta nu))
    (hForward : ∀ nu a, ((g.chart nu a) : P × M → P × Es) = g0.chart nu a)
    (hInverse : ∀ nu a, ((g.chart nu a).symm : P × Es → P × M) = (g0.chart nu a).symm)
    (hAll : Ref.parameterSet = univ)
    (ell cT : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (SampleInverse SampleForward OldMeta : ℕ → ℝ) (Rsub Lprimary : ℕ)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount) :
    let E := round3ParameterStageData Ref F H V normal domain neighborhood
    ∀ (hd : IncrementsOriginalDomainConditions E) (hs : IncrementsOriginalSmoothInputs E)
      (hn : IncrementsOriginalFreeNormalConditions E hd hs),
    Round3ParameterOriginalNativeMeanPreparation E hd hs hn g ell cT
      SampleInverse SampleForward OldMeta Rsub Lprimary i →
    Round3ParameterOriginalNativeMeanPreparation E hd hs hn g ell cT
      SampleInverse SampleForward
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) Rsub Lprimary i := by
  intro E hd hs hn prep
  let gN := round3ParameterNativePrimary (fun p x => F (p,x)) g (Ref.parameterChart i.2)
  let gLocal := actualOriginalPrimaryFamily E hd hs hn i prep.host prep.native prep.slices prep.data
    gN.eta prep.active
  have hEq := round3Parameter_original_open_slice_eq_global E hd hAll i
  have hOriginal := (round3Parameter_refinement_samples_heq E i.2 hEq gLocal gN prep.same
    prep.host prep.native ((Ref.parameterChart i.2).target ×ˢ (univ : Set M)) ell
    SampleInverse SampleForward OldMeta Rsub Lprimary).mp prep.refinement
  have hNew := round4_actual_rebound_refinement_sample_meta Ref g0 R geom Forward Inverse Meta
    hProfiles F H V normal domain neighborhood g hCutoff hEta hForward hInverse i.2 prep.host prep.native
    ((Ref.parameterChart i.2).target ×ˢ (univ : Set M))
    ((Ref.parameterChart i.2).open_target.prod isOpen_univ) Subset.rfl ell hell hell1
    SampleInverse SampleForward OldMeta Rsub Lprimary hOriginal
  refine { prep with refinement := ?_ }
  exact (round3Parameter_refinement_samples_heq E i.2 hEq gLocal gN prep.same
    prep.host prep.native ((Ref.parameterChart i.2).target ×ˢ (univ : Set M)) ell
    SampleInverse SampleForward
    (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) Rsub Lprimary).mpr hNew

#print axioms round4_actual_rebound_native_mean_preparation
end GlobalEmbedding.Continuation
