import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

section
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad

private theorem mem_letters' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, i⟩ := x
  obtain ⟨a, rfl⟩ := (Fintype.equivFin (E →+* ℂ)).symm.surjective τ
  unfold letters
  exact List.mem_flatMap.2 ⟨a, List.mem_finRange _, List.mem_map.2 ⟨i, List.mem_finRange _, rfl⟩⟩

private theorem nodup_letters' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) : (letters Dw).Nodup := by
  unfold letters
  rw [List.nodup_flatMap]
  refine ⟨fun a _ => (List.nodup_finRange _).map fun i j h => ?_, ?_⟩
  · exact eq_of_heq (Sigma.mk.inj_iff.1 h).2
  · refine (List.nodup_finRange _).imp ?_
    intro a b hab
    simp only [Function.onFun]
    intro x hx hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, -, h⟩ := List.mem_map.1 hy
    exact hab ((Fintype.equivFin (E →+* ℂ)).symm.injective (congrArg Sigma.fst h)).symm

private theorem exists_mul_mem' {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (v : V)
    (hv : v ∈ Submodule.span K (L : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ L := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, he, hy⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hx
    · rw [mul_smul]; exact L.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨⟨e, he⟩, b, hb⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) a
    refine ⟨e * d, mul_ne_zero (nonZeroDivisors.ne_zero he) hd, ?_⟩
    have : (e * d) • a • x = b • d • x := by
      rw [mul_comm, mul_smul, ← smul_assoc e a x, show e • a = algebraMap _ K b from hb.symm, algebraMap_smul, smul_comm]
    rw [this]
    exact L.smul_mem _ hx

end

open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead in
