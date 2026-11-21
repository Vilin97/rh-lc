module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUnipotentInCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnipExhaust

theorem exists_compact_subgroup_between {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N : ℕ} {U : Subgroup (GL (Fin N) k)}
    (hU : U ≤ unipB k (Fin N)) (hcl : IsClosed (U : Set (GL (Fin N) k)))
    (Q : Set (GL (Fin N) k)) (hQ : IsCompact Q) (hQU : Q ⊆ (U : Set (GL (Fin N) k))) :
    ∃ L : {L : Subgroup (GL (Fin N) k) // IsCompact (L : Set (GL (Fin N) k)) ∧ L ≤ U},
      Q ⊆ (L.1 : Set (GL (Fin N) k)) := by
  have hex : ∃ U₀ : Subgroup (GL (Fin N) k), IsCompact (U₀ : Set (GL (Fin N) k)) ∧
      Q ⊆ (U₀ : Set (GL (Fin N) k)) := by
    set c : Fin N → ℤ := fun i => ((i : ℕ) : ℤ)
    have hQun : Q ⊆ (unipOf k c : Set (GL (Fin N) k)) := by
      intro g hg
      rw [← GlobalTheory.UnipCptSub.unipB_eq_unipOf N]
      exact hU (hQU hg)
    let V : ℕ → Set (GL (Fin N) k) := fun m =>
      (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL (Fin N) k)) ∪ (unipOf k c : Set _)ᶜ
    have hVo : ∀ m, IsOpen (V m) := fun m =>
      (GlobalTheory.UnipCptSub.isOpen_grp c m).union (GlobalTheory.UnipCompact.isClosed_unipOf c).isOpen_compl
    have hVmono : Monotone V := by
      intro m M hmM g hg
      rcases hg with hg | hg
      · by_cases hu : g ∈ unipOf k c
        · exact Or.inl (GlobalTheory.UnipCptSub.mem_grp_of_le hu hmM hg)
        · exact Or.inr hu
      · exact Or.inr hg
    have hcov : Q ⊆ ⋃ m, V m := fun g hg =>
      Set.mem_iUnion.2 (((GlobalTheory.UnipCompact.eventually_mem_grp (hQun hg)).exists).imp fun _ h => Or.inl h)
    obtain ⟨M, hM⟩ := hQ.elim_directed_cover V hVo hcov hVmono.directed_le
    refine ⟨GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) ⊓ unipOf k c, ?_, fun g hg => ?_⟩
    · rw [Subgroup.coe_inf]
      exact (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right (GlobalTheory.UnipCompact.isClosed_unipOf c)
    · rcases hM hg with h | h
      · exact ⟨h, hQun hg⟩
      · exact absurd (hQun hg) h
  obtain ⟨U₀, hc, hs⟩ := hex
  refine ⟨⟨U₀ ⊓ U, ?_, inf_le_right⟩, fun g hg => ⟨hs hg, hQU hg⟩⟩
  rw [Subgroup.coe_inf]
  exact hc.inter_right hcl

theorem exists_monotone_compact_exhaustion :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
      (U : Subgroup (GL (Fin N) k)), U ≤ unipB k (Fin N) → IsClosed (U : Set (GL (Fin N) k)) →
      ∃ L : ℕ → Subgroup (GL (Fin N) k), Monotone L ∧ (∀ j, IsCompact (L j : Set (GL (Fin N) k))) ∧
        (∀ j, L j ≤ U) ∧ ∀ n ∈ U, ∃ j, n ∈ L j := by
  intro k _ _ _ _ N U hU hcl
  haveI : SecondCountableTopology (GL (Fin N) k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : LocallyCompactSpace (GL (Fin N) k) := GlobalTheory.SplitFlip.locallyCompact_GL
  haveI : SigmaCompactSpace (GL (Fin N) k) := inferInstance
  let S := {L : Subgroup (GL (Fin N) k) // IsCompact (L : Set (GL (Fin N) k)) ∧ L ≤ U}
  let K : ℕ → Set (GL (Fin N) k) := compactCovering (GL (Fin N) k)
  have hstep : ∀ (j : ℕ) (A : S), ∃ B : S,
      (K j ∩ (U : Set (GL (Fin N) k))) ∪ (A.1 : Set (GL (Fin N) k)) ⊆ (B.1 : Set (GL (Fin N) k)) :=
    fun j A => exists_compact_subgroup_between hU hcl _
      (((isCompact_compactCovering _ j).inter_right hcl).union A.2.1)
      (Set.union_subset Set.inter_subset_right A.2.2)
  choose next hnext using hstep
  let b : S := ⟨⊥, by rw [Subgroup.coe_bot]; exact isCompact_singleton, bot_le⟩
  let f : ℕ → S := fun j => Nat.rec b (fun i A => next i A) j
  have hsucc : ∀ j, f (j + 1) = next j (f j) := fun _ => rfl
  refine ⟨fun j => (f j).1, monotone_nat_of_le_succ fun j g hg => ?_, fun j => (f j).2.1,
    fun j => (f j).2.2, fun n hn => ?_⟩
  · rw [hsucc]
    exact hnext j (f j) (Or.inr hg)
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1
      ((iUnion_compactCovering (GL (Fin N) k)).symm ▸ Set.mem_univ n : n ∈ ⋃ i, K i)
    refine ⟨j + 1, ?_⟩
    show n ∈ (f (j + 1)).1
    rw [hsucc]
    exact hnext j (f j) (Or.inl ⟨hj, hn⟩)

end GlobalTheory.CompanionTheory.UnipExhaust
