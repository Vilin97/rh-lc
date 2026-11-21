module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantScaledLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledIntegralFiniteAdelePointsSubsetNhds
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_invariant_scaled_lattice : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ d : F, d ≠ 0 ∧ ∀ y, ∀ u ∈ GlobalTheory.EvAdm.scaledInt F κ d, g (y + u) = g y := by
  intro F _ _ κ _ g hg
  obtain ⟨hlc, hcs⟩ := hg
  have hW : ∀ y, {z | g (y + z) = g y} ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) := fun y =>
    ((hlc.isOpen_fiber (g y)).preimage (continuous_const.add continuous_id)).mem_nhds (by simp)
  choose b hb hbW using fun y => GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds F κ _ (hW y)
  have hN : ∀ y ∈ tsupport g, {x | x - y ∈ GlobalTheory.EvAdm.scaledInt F κ (b y)} ∈ 𝓝 y := fun y _ =>
    ((GlobalTheory.EvAdm.isOpen_scaledInt (b y)).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover hcs _ hN
  have hW0 : (⋂ y ∈ t, (GlobalTheory.EvAdm.scaledInt F κ (b y) : Set (κ → FiniteAdeleRing (𝓞 F) F))) ∈
      𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
    (Filter.biInter_finset_mem t).2 fun y _ => (GlobalTheory.EvAdm.isOpen_scaledInt (b y)).mem_nhds (zero_mem _)
  obtain ⟨a, ha, haW⟩ := GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds F κ _ hW0
  refine ⟨a, ha, fun x z hz => ?_⟩
  have key : ∀ y ∈ t, x - y ∈ GlobalTheory.EvAdm.scaledInt F κ (b y) → g (x + z) = g x := fun y hy hxy => by
    have hz' : z ∈ GlobalTheory.EvAdm.scaledInt F κ (b y) := Set.mem_iInter₂.1 (haW hz) y hy
    have h1 : g (y + (x - y)) = g y := hbW y hxy
    have h2 : g (y + (x - y + z)) = g y := hbW y (add_mem hxy hz')
    rw [add_sub_cancel] at h1
    rw [show y + (x - y + z) = x + z by abel] at h2
    rw [h1, h2]
  by_cases hx : x ∈ tsupport g
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact key y hy hxy
  by_cases hxz : x + z ∈ tsupport g
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hxz)
    have hz' : z ∈ GlobalTheory.EvAdm.scaledInt F κ (b y) := Set.mem_iInter₂.1 (haW hz) y hy
    refine key y hy ?_
    have := sub_mem hxy hz'
    rwa [show x + z - y - z = x - y by abel] at this
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxz]

