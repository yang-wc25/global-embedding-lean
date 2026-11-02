import Probes.Round3ParameterRawAtlasData
import Probes.ActualIncrementRawJointRegularity

/-! Joint smoothness of one actual global U on an entire common physical
domain.  Native chart consumers observe the same canonical U; a genuine
parameter-atlas cover returns their regularity to P×M.  For W=univ this is
global smoothness, with no intersection of stage-dependent neighborhoods. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

section Topology
variable {P Q M : Type*} [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace M]
theorem round3ParameterNativeDomain_open
    (B : OpenPartialHomeomorph P Q) (W : Set (P × M)) (hW : IsOpen W) :
    IsOpen (round3ParameterNativeDomain B W) := by
  have hk : ContinuousOn (fun z : Q × M => (B.symm z.1,z.2)) (B.target ×ˢ (Set.univ : Set M)) :=
    (B.symm.continuousOn.comp continuous_fst.continuousOn (fun z hz => hz.1)).prodMk
      continuous_snd.continuousOn
  simpa only [round3ParameterNativeDomain,Set.inter_def,Set.mem_prod,Set.mem_univ,and_true,
    Set.mem_setOf_eq,Set.mem_preimage] using
    hk.isOpen_inter_preimage (B.open_target.prod isOpen_univ) hW
end Topology

section Atlas
variable {m d N c : ℕ} {P M : Type*} [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_contMDiffOn_of_native_atlas
    (B : Fin c → OpenPartialHomeomorph P Ep)
    (hB : ∀ b, B b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (W : Set (P × M)) (hW : IsOpen W)
    (cover : ∀ z ∈ W, ∃ b, z.1 ∈ (B b).source)
    (U : P × M → V) (native : Fin c → Ep × M → V)
    (heq : ∀ b t, t ∈ (B b).target → ∀ x,
      native b (t,x) = U ((B b).symm t,x))
    (hreg : ∀ b, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞
      (native b) (round3ParameterNativeDomain (B b) W)) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ U W := by
  intro z hz
  obtain ⟨b,hb⟩ := cover z hz
  have hn : ((B b) z.1,z.2) ∈ round3ParameterNativeDomain (B b) W := by
    exact ⟨(B b).map_source hb,by simpa only [(B b).left_inv hb] using hz⟩
  have hchart : ContMDiffAt ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (fun y : P × M => ((B b) y.1,y.2)) z :=
    ((contMDiffAt_of_mem_maximalAtlas (hB b) hb).comp z contMDiffAt_fst).prodMk contMDiffAt_snd
  have hcomp := ((hreg b).contMDiffAt ((round3ParameterNativeDomain_open (B b) W hW).mem_nhds hn)).comp z hchart
  apply (hcomp.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [((B b).open_source.preimage continuous_fst).mem_nhds hb] with y hy
  change U y = native b ((B b) y.1,y.2)
  rw [heq b ((B b) y.1) ((B b).map_source hy) y.2,(B b).left_inv hy]

variable [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Tr Label SubPrimary SubSecondary : Type*}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]

theorem round3Parameter_actual_increment_joint_contMDiffOn
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k)
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (hB : ∀ b, B b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := SubPrimary) F)
    (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
    (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (W : Set (P × M)) (hW : IsOpen W) (cover : ∀ z ∈ W, ∃ b, z.1 ∈ (B b).source)
    (primary : Label → Set (P × M))
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (ell delta tau Delta : ℝ) (htau : 0 < tau)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
    (hc : ∀ r a, Round3ParameterChartPreserves (choice r a).chart)
    (data : Round3ParameterRawAtlasData (Tr := Tr) A B F hF g input inputbar
      nInput nSolve j q Rsub Lprimary Rsecondary reserve Bnd Mg Kcut T Tinv Tobs
      W primary S ell delta tau Delta choice) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞
      (round3ParameterIncrementMap F hF g input (q+2) tau delta choice) W := by
  apply round3Parameter_contMDiffOn_of_native_atlas B hB W hW cover
    (round3ParameterIncrementMap F hF g input (q+2) tau delta choice)
    (fun b => actualOriginalIncrementMap (fun t => F ((B b).symm t)) (fun t => hF ((B b).symm t))
      (round3ParameterNativePrimary F g (B b)) (fun t => input ((B b).symm t)) (q+2) tau delta
      (round3ParameterNativeChoices choice (B b)))
  · intro b t ht x
    exact round3Parameter_native_increment_eq F hF g (B b) hg input (q+2) tau delta choice hc t ht x
  · intro b z hz
    obtain ⟨a,_ha⟩ := A.cover z.2
    exact (actual_original_increment_raw_joint_contMDiffOn nInput nSolve j q Rsub Lprimary hq hInput
      reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv hT hTinv
      (fun t => F ((B b).symm t)) (fun t => hF ((B b).symm t))
      (round3ParameterNativePrimary F g (B b))
      (fun t => input ((B b).symm t)) (fun t => inputbar ((B b).symm t))
      (round3ParameterNativeDomain (B b) W) (fun ν => round3ParameterNativeDomain (B b) (primary ν))
      ell delta tau Delta htau (data.observation (a,b)).profiles.prim
      (round3ParameterNativeChoices choice (B b)) (data.raw b)) z hz

end Atlas
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_increment_joint_contMDiffOn
