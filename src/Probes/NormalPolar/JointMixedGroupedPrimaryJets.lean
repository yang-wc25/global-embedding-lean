import NormalPolar.JointMixedGroupedPrimary
import NormalPolar.JointMixedGroupedVariablePhysical
import NormalPolar.ParameterDisplacementPrescribedVariableJets
import Probes.ActualIncrementRawPrimaryWave
import Probes.Round4ParameterProbeCombinedPrimary

/-!
# Joint primary jets from the actual raw inputs

The background input is a single joint tensor field. The prescribed parameter
is substituted into the full physical wave before differentiation. Thus the
Leibniz derivatives of that parameter are included, while the complete solver
channels and the actual background reconstruction are retained.

The constant is selected before all maps, scales and raw inputs. Neither
primary-wave jets nor a completed first-increment estimate is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)] {Ep M Tr Λ Β : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

theorem jointGrouped_primary_raw_jets_uniform
    (n backgroundLength probeLength j Rbackground L Rprobe : ℕ)
    (hbackgroundOrder : j+2+backgroundLength ≤ n) (hprobeOrder : j+2+probeLength ≤ n)
    (reserve Bnd Mg Bchi Bnu Ku Mphase : ℝ)
    (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku)
    (weight : Fin r → ℝ) (Tbackground Tprobe : ℕ → ℝ)
    (hTbackground : ∀ k, 0 ≤ Tbackground k) (hTprobe : ∀ k, 0 ≤ Tprobe k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (label : (Fin r × Bool) ↪ Fin p)
      (c : (l : Fin r) → Pieces l → Ep → D → M) (chi : (l : Fin r) → Pieces l → X → ℝ)
      (nu : (l : Fin r) → (s : Pieces l) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
      (phase : Fin r → Ep × M → ℝ) (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (Ep × M) X)
      (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (tau ell delta Delta : ℝ) (hdelta : 0 ≤ delta)
      (W : Set (Ep × M)) (K : (Λ ⊕ Fin r) → Set (Ep × M))
      (pieceK : (l : Fin r) → Pieces l → Set (Ep × M))
    (hpieceK : ∀ l s, pieceK l s ⊆ K (Sum.inr l))
    (e : OpenPartialHomeomorph M D) (Omega S : Set X)
      (background : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n backgroundLength j Rbackground L
        reserve Bnd Mg Tbackground F hF g input inputbar W (fun l => K (Sum.inl l)) e Omega S tau ell Delta)
      (hadapt : ∀ l q z, z ∈ (g.chart l q).source → g.phase l z = (g.chart l q z).2 0)
      (prescribed : JointGroupedPrescribedObservationProfiles F hF c chi nu a W pieceK
        n (j+1) ell Mg Bchi Bnu (fun z : X => (z.1,e.symm z.2)) Omega S Tprobe phase Mphase)
      (hcount : ∀ y ∈ S, (Finset.univ.filter (fun l => (y.1,e.symm y.2) ∈ K l)).card ≤ L)
      (hRprobe : ∀ l y, y ∈ S → (Finset.univ.filter (fun s => (y.1,e.symm y.2) ∈ pieceK l s)).card ≤ Rprobe)
    (u : Ep → Fin p → ℝ)
      (hu : ContDiffOn ℝ ∞ (fun z : X => u z.1) Omega)
      (hub : ∀ k ≤ j+1, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun y : X => u y.1) z‖ ≤ Ku),
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let U1 := fun z : X => jointGroupedCombinedPrimary F hF g label c vf phase
      tau delta backgroundLength probeLength a input (u z.1) (z.1,e.symm z.2)
    ContDiffOn ℝ ∞ U1 Omega ∧ ∀ k ≤ j+1, ∀ y ∈ S,
      tau^k*‖iteratedFDeriv ℝ k U1 y‖ ≤ C*delta*tau := by
  obtain ⟨Cbackground,hCbackground,hbackground⟩ := actual_original_primary_wave_from_raw_uniform
    (I := IM) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N) (Λ := Λ) (Β := Β)
    n backgroundLength j Rbackground L hbackgroundOrder reserve Bnd Mg hreserve hBnd hMg Tbackground hTbackground
  let Cprobe := actualVariablePrescribedWaveCost m N p n probeLength (j+1) (L*Rprobe)
    Tprobe weight Mg Bchi Bnu Mphase Ku
  have hCprobe : 0 ≤ Cprobe := actualVariablePrescribedWaveCost_nonneg
    m N p n probeLength (j+1) (L*Rprobe) Tprobe weight Mg Bchi Bnu Mphase Ku hTprobe hMg hBchi hBnu hKu
  refine ⟨Cbackground+Cprobe,add_nonneg hCbackground hCprobe,?_⟩
  intro F hF g label c chi nu phase a input inputbar tau ell delta Delta hdelta
    W K pieceK hpieceK e Omega S background hadapt prescribed hcount hRprobe u hu hub vf U1
  let kappa := fun z : X => (z.1,e.symm z.2)
  let bg := fun z : X => delta • incrementsGlobalPrimaryWave F hF g input backgroundLength tau (kappa z)
  let pr := fun z : X => jointGroupedPrescribedWave label F hF c vf phase tau probeLength a (u z.1) (kappa z)
  have hLprobe (y : X) (hy : y ∈ S) :
      (Finset.univ.filter (fun l : Fin r => kappa y ∈ K (Sum.inr l))).card ≤ L := by
    apply (Finset.card_le_card_of_injOn (Sum.inr : Fin r → Λ ⊕ Fin r) ?_ ?_).trans (hcount y hy)
    · intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
    · intro l _ q _ h
      exact Sum.inr.inj h
  have hb := hbackground F hF g input inputbar W (fun l => K (Sum.inl l))
    e Omega S tau ell Delta background hadapt
  have hbg : ContDiffOn ℝ ∞ bg Omega := hb.1.const_smul delta
  have hp := jointGrouped_prescribed_variable_parameter_raw_jets label F hF c chi nu a W
    (fun l => K (Sum.inr l)) pieceK background.prim.hW hpieceK n probeLength (j+1) (by omega)
    tau ell delta weight Mg Bchi Bnu Ku background.htau background.htaul background.hell1
    hMg hdelta hBchi hBnu hKu kappa Omega S background.hO background.hSO
    background.hkappaO background.hmapWO Tprobe hTprobe phase Mphase prescribed
    L Rprobe hLprobe hRprobe (fun z : X => u z.1) hu hub
  have heq : U1 = fun z => bg z+pr z := by
    funext z
    exact jointGroupedCombinedPrimary_eq F hF g label c vf phase tau delta
      backgroundLength probeLength a input (u z.1) (kappa z)
  rw [heq]
  refine ⟨hbg.add hp.1,?_⟩
  intro k hk y hy
  have hmem := background.hO.mem_nhds (background.hSO hy)
  have hbgj : tau^k*‖iteratedFDeriv ℝ k bg y‖ ≤ Cbackground*delta*tau := by
    simpa only [abs_of_nonneg hdelta] using hb.2 delta k hk y hy
  exact (actual_joint_slow_add_jet_bound bg pr k tau (Cbackground*delta*tau) (Cprobe*delta*tau)
    background.htau.le y ((hbg.contDiffAt hmem).of_le (by simp)) ((hp.1.contDiffAt hmem).of_le (by simp))
    hbgj (hp.2 k hk y hy)).trans_eq (by ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointGrouped_primary_raw_jets_uniform
