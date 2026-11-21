module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder

@[expose] public section

open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sub_mem_maximalIdeal_pointedEtaleNeighbourhood :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (b : i.B),
      ∃ r : R, b - algebraMap R i.B r ∈ maximalIdeal i.B := by
  intro R _ _ i b
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective i.q.primeCompl b
  obtain ⟨r₁, hr₁⟩ := residue_surjective (i.pt a)
  obtain ⟨r₂, hr₂⟩ := residue_surjective (i.pt (s : i.A))
  have hs : i.pt (s : i.A) ≠ 0 := by
    intro h
    exact s.2 (show (s : i.A) ∈ RingHom.ker i.pt from h)
  have hu : IsUnit r₂ := by
    by_contra hn
    exact hs (hr₂ ▸ (residue_eq_zero_iff r₂).2 ((mem_maximalIdeal r₂).2 hn))
  obtain ⟨u, rfl⟩ := hu
  let r := r₁ * ((u⁻¹ : Rˣ) : R)
  refine ⟨r, ?_⟩
  have hsub : IsLocalization.mk' i.B a s - algebraMap R i.B r =
      IsLocalization.mk' i.B (a - (s : i.A) * algebraMap R i.A r) s := by
    rw [IsLocalization.eq_mk'_iff_mul_eq, sub_mul, IsLocalization.mk'_spec,
      (algebraMap i.A i.B).map_sub, (algebraMap i.A i.B).map_mul,
      ← IsScalarTower.algebraMap_apply R i.A i.B, mul_comm (algebraMap R i.B r)]
  rw [hsub, IsLocalization.AtPrime.mk'_mem_maximal_iff (S := i.B) (I := i.q)]
  change a - (s : i.A) * algebraMap R i.A r ∈ RingHom.ker i.pt
  rw [RingHom.mem_ker, map_sub, map_mul, AlgHom.commutes, ← hr₁, ← hr₂,
    ResidueField.algebraMap_eq, ← map_mul, ← map_sub]
  simp [r, mul_left_comm (↑u : R) r₁]
