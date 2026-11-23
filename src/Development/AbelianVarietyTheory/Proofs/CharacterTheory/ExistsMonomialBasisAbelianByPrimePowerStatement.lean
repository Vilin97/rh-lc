module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CommuteImageAbelianByPrimePowerOfNormalCentral
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
public import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsAbelianByPrimePowerGroupSubgroup
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Sheaves.Presheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsMonomialBasisOfImprimitive

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem exists_monomial_basis_of_imprimitive (k : Type) [Field k] (G : Type) [Group G] [Finite G]
    (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
    (T : Subgroup G) (W : Submodule k V)
    (hind : iSupIndep (fun q : G ⧸ T => W.map (ρ q.out)))
    (hsup : ⨆ q : G ⧸ T, W.map (ρ q.out) = ⊤)
    (hW : ∃ (n : ℕ) (b : Module.Basis (Fin n) k W), ∀ t ∈ T, ∀ i : Fin n,
      ∃ (j : Fin n) (c : k), ρ t (b i : V) = c • (b j : V)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  classical
  obtain ⟨n, b, hb⟩ := hW
  have hinj : ∀ g : G, Function.Injective (ρ g) := by
    intro g x y h
    have h2 := congrArg (ρ g⁻¹) h
    simpa [← Module.End.mul_apply, ← map_mul] using h2
  have hint : DirectSum.IsInternal (fun q : G ⧸ T => W.map (ρ q.out)) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup
  let bq : ∀ q : G ⧸ T, Module.Basis (Fin n) k (W.map (ρ q.out)) := fun q =>
    b.map (Submodule.equivMapOfInjective (ρ q.out) (hinj _) W)
  let B := hint.collectedBasis bq
  have hB : ∀ (q : G ⧸ T) (i : Fin n), B ⟨q, i⟩ = ρ q.out (b i : V) := by
    intro q i
    simp [B, bq]
  haveI : Fintype (G ⧸ T) := Fintype.ofFinite _
  let e := Fintype.equivFin (Σ _ : G ⧸ T, Fin n)
  refine ⟨_, B.reindex e, fun g i => ?_⟩
  obtain ⟨⟨q, i⟩, rfl⟩ := e.surjective i
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T (g * q.out)
  obtain ⟨j, c, hj⟩ := hb (t⁻¹ : T) (t⁻¹).2 i
  refine ⟨e ⟨(QuotientGroup.mk (g * q.out) : G ⧸ T), j⟩, c, ?_⟩
  simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, hB]
  rw [← map_smul, ← hj, ht, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  simp

end GlobalTheory.CuspGL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantEqTopOfIrreducible

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

theorem invariant_eq_top_of_irreducible {k : Type} [Field k] {G : Type} [Group G] {V : Type}
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (h : ρ.IsIrreducible)
    (U : Submodule k V) (hU : ∀ g, ∀ v ∈ U, ρ g v ∈ U) (v : V) (hv : v ∈ U) (hv0 : v ≠ 0) :
    U = ⊤ := by
  rcases h.eq_bot_or_eq_top (⟨U, fun g v hv => hU g v hv⟩ : Subrepresentation ρ) with H | H
  · have H' : U = ⊥ := congrArg Subrepresentation.toSubmodule H
    exact absurd (by simpa [H'] using hv) hv0
  · exact congrArg Subrepresentation.toSubmodule H

theorem finrank_eq_one_or_imprimitive : ∀ (k : Type) [Field k] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k], AbByP G → ρ.IsIrreducible → Module.finrank k V = 1 ∨ ∃ (T : Subgroup G) (W : Submodule k V), T ≠ ⊤ ∧ (∀ t ∈ T, ∀ w ∈ W, ρ t w ∈ W) ∧ iSupIndep (fun q : G ⧸ T => W.map (ρ q.out)) ∧ ⨆ q : G ⧸ T, W.map (ρ q.out) = ⊤ := by
  intro k _ G _ _ V _ _ _ ρ _ hG hirr
  haveI : Nontrivial V := by
    have h1 : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
    have h2 : (⊥ : Submodule k V) ≠ ⊤ := fun H => h1 (Subrepresentation.ext H)
    exact (Submodule.nontrivial_iff k).1 ⟨_, _, h2⟩
  by_cases hc : ∀ a b : G, ρ a * ρ b = ρ b * ρ a
  · left
    obtain ⟨v, hv0, hv⟩ := GlobalTheory.exists_common_eigenvector_of_commute (fun g : G => ρ g) hc
    have htop := invariant_eq_top_of_irreducible ρ hirr (Submodule.span k {v}) (by
      intro g w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      obtain ⟨m, hm⟩ := hv g
      rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      have hm' : ρ g v = m • v := hm
      rw [hm']
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
      v (Submodule.mem_span_singleton_self v) hv0
    rw [← finrank_top, ← htop, finrank_span_singleton hv0]
  right
  have hB : ¬ ∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, ρ a * ρ b = ρ b * ρ a) →
      ∀ b ∈ B, ∀ g : G, ρ b * ρ g = ρ g * ρ b := fun H => hc (commute_all G _ ρ hG H)
  push Not at hB
  obtain ⟨B, hBn, hBc, b₀, hb₀, g₀, hne⟩ := hB
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.exists_common_eigenvector_of_commute (fun b : B => ρ b)
    (fun a b => hBc a a.2 b b.2)
  choose μ hμ using hv
  let c : G →* MulAut B := MulAut.conjNormal
  have hcv : ∀ (g : G) (b : B), ((c g b : B) : G) = g * b * g⁻¹ := fun g b => rfl
  let E : (B → k) → Submodule k V := fun χ => ⨅ b : B, Module.End.eigenspace (ρ b) (χ b)
  have hE : ∀ χ w, w ∈ E χ ↔ ∀ b : B, ρ b w = χ b • w := by
    intro χ w
    simp only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hind : iSupIndep E :=
    (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun b : B => ρ b)
      fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hBc j j.2 i i.2) φ).mono fun _ =>
        iInf_mono fun i => (Module.End.genEigenspace (ρ i) _).monotone le_top
  have hmap : ∀ (g : G) (w : V), w ∈ E μ → ρ g w ∈ E (fun b => μ (c g⁻¹ b)) := by
    intro g w hw
    rw [hE] at hw ⊢
    intro b
    rw [← map_smul, ← hw, hcv, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
      ← map_mul]
    congr 2
    group
  let T : Subgroup G :=
    { carrier := {g | ∀ b, μ (c g b) = μ b}
      one_mem' := fun b => by simp
      mul_mem' := fun {x y} hx hy b => by
        rw [map_mul, MulAut.mul_apply, hx, hy]
      inv_mem' := fun {x} hx b => by
        rw [← hx, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] }
  have hT : ∀ g, g ∈ T ↔ ∀ b, μ (c g b) = μ b := fun g => Iff.rfl
  have hstab : ∀ t ∈ T, ∀ w ∈ E μ, ρ t w ∈ E μ := by
    intro t ht w hw
    have h1 := hmap t w hw
    have h2 : (fun b => μ (c t⁻¹ b)) = μ := funext ((hT _).1 (T.inv_mem ht))
    rwa [h2] at h1
  have hvE : v ∈ E μ := (hE _ _).2 hμ
  refine ⟨T, E μ, ?_, hstab, ?_, ?_⟩
  · intro hTop
    have htop := invariant_eq_top_of_irreducible ρ hirr (E μ)
      (fun g w hw => hstab g (hTop ▸ Subgroup.mem_top g) w hw) v hvE hv0
    have hs : ∀ w, ρ b₀ w = μ ⟨b₀, hb₀⟩ • w := fun w =>
      (hE μ w).1 (htop ▸ Submodule.mem_top) ⟨b₀, hb₀⟩
    apply hne
    ext w
    simp only [Module.End.mul_apply, hs, map_smul]
  · have hinj : Function.Injective fun q : G ⧸ T => fun b => μ (c q.out⁻¹ b) := by
      intro q q' hq
      rw [← q.out_eq, ← q'.out_eq]
      refine QuotientGroup.eq.2 ((hT _).2 fun b => ?_)
      have h1 : μ (c q.out⁻¹ (c q'.out b)) = μ (c q'.out⁻¹ (c q'.out b)) := congrFun hq _
      rw [map_mul, MulAut.mul_apply, h1, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        MulAut.one_apply]
    refine (hind.comp hinj).mono fun q => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hmap _ w hw
  · have hmem : ∀ (g : G) (w : V), w ∈ E μ → ρ g w ∈ ⨆ q : G ⧸ T, (E μ).map (ρ q.out) := by
      intro g w hw
      obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T g
      refine Submodule.mem_iSup_of_mem (g : G ⧸ T) ⟨ρ (t⁻¹ : G) w, hstab _ (T.inv_mem t.2) w hw, ?_⟩
      rw [ht, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
    refine invariant_eq_top_of_irreducible ρ hirr _ ?_ v (by simpa using hmem 1 v hvE) hv0
    intro g w hw
    have hle : (⨆ q : G ⧸ T, (E μ).map (ρ q.out)) ≤
        (⨆ q : G ⧸ T, (E μ).map (ρ q.out)).comap (ρ g) := by
      refine iSup_le fun q => ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
      exact hmem _ u hu
    exact hle hw

end GlobalTheory.BI
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsMonomialBasisAbelianByPrimePower

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem exists_monomial_basis_of_isCompl {k : Type} [Field k] {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (U U' : Submodule k V) (h : IsCompl U U')
    (hU : ∃ (n : ℕ) (b : Module.Basis (Fin n) k U), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V))
    (hU' : ∃ (n : ℕ) (b : Module.Basis (Fin n) k U'), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  obtain ⟨n, b, hb⟩ := hU
  obtain ⟨n', b', hb'⟩ := hU'
  let B := (b.prod b').map (Submodule.prodEquivOfIsCompl U U' h)
  have h1 : ∀ i, B (Sum.inl i) = (b i : V) := by
    intro i
    simp [B, Module.Basis.prod_apply]
  have h2 : ∀ i, B (Sum.inr i) = (b' i : V) := by
    intro i
    simp [B, Module.Basis.prod_apply]
  refine ⟨n + n', B.reindex finSumFinEquiv, fun g i => ?_⟩
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i
  · obtain ⟨j, c, hj⟩ := hb g i
    refine ⟨finSumFinEquiv (Sum.inl j), c, ?_⟩
    simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, h1, hj]
  · obtain ⟨j, c, hj⟩ := hb' g i
    refine ⟨finSumFinEquiv (Sum.inr j), c, ?_⟩
    simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, h2, hj]

theorem exists_monomial_basis_of_abByP : ∀ (k : Type) [Field k] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k], AbByP G → (Nat.card G : k) ≠ 0 → ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n), ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  intro k _
  have key : ∀ (m : ℕ) (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k],
      Nat.card G + Module.finrank k V = m → AbByP G → (Nat.card G : k) ≠ 0 →
      ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
        ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro G _ _ V _ _ _ ρ _ hm hG hcard
    by_cases h0 : Module.finrank k V = 0
    · exact ⟨0, Module.finBasisOfFinrankEq k V h0, fun g i => i.elim0⟩
    by_cases hirr : ρ.IsIrreducible
    · rcases finrank_eq_one_or_imprimitive k G V ρ hG hirr with h1 | ⟨T, W, hT, hW, hind, hsup⟩
      · let b := Module.finBasisOfFinrankEq k V h1
        refine ⟨1, b, fun g i => ⟨0, b.repr (ρ g (b i)) 0, ?_⟩⟩
        have := b.sum_repr (ρ g (b i))
        rw [Fin.sum_univ_one] at this
        exact this.symm
      · refine exists_monomial_basis_of_imprimitive k G V ρ T W hind hsup ?_
        let σ : Subrepresentation (ρ.comp T.subtype : Representation k T V) :=
          ⟨W, fun t w hw => hW t t.2 w hw⟩
        have hlt : Nat.card T < Nat.card G := by
          have := T.card_le_card_group
          have h2 : Nat.card T ≠ Nat.card G := fun H => hT (Subgroup.eq_top_of_card_eq T H)
          omega
        have hle : Module.finrank k W ≤ Module.finrank k V := Submodule.finrank_le W
        have hc : (Nat.card T : k) ≠ 0 := by
          intro H
          obtain ⟨d, hd⟩ := T.card_subgroup_dvd_card
          apply hcard
          rw [hd, Nat.cast_mul, H, zero_mul]
        obtain ⟨n, b, hb⟩ := ih _ (by omega) T W σ.toRepresentation rfl (AbByP.subgroup G T hG) hc
        refine ⟨n, b, fun t ht i => ?_⟩
        obtain ⟨j, c, hj⟩ := hb ⟨t, ht⟩ i
        exact ⟨j, c, congrArg Subtype.val hj⟩
    · haveI : NeZero (Nat.card G : k) := ⟨hcard⟩
      haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero h0)
      haveI : Nontrivial (Subrepresentation ρ) :=
        ⟨⊥, ⊤, fun H => (bot_ne_top : (⊥ : Submodule k V) ≠ ⊤)
          (congrArg Subrepresentation.toSubmodule H)⟩
      have hex : ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U ≠ ⊤ := by
        by_contra H
        push Not at H
        exact hirr ⟨fun U => by
          by_cases hU : U = ⊥
          · exact Or.inl hU
          · exact Or.inr (H U hU)⟩
      obtain ⟨U, hU0, hU1⟩ := hex
      obtain ⟨U', hUU'⟩ := exists_isCompl U
      have hcompl : IsCompl U.toSubmodule U'.toSubmodule :=
        ⟨disjoint_iff.2 (congrArg Subrepresentation.toSubmodule hUU'.inf_eq_bot),
          codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule hUU'.sup_eq_top)⟩
      have hsub : ∀ S : Subrepresentation ρ, S ≠ ⊤ →
          ∃ (n : ℕ) (b : Module.Basis (Fin n) k S.toSubmodule), ∀ (g : G) (i : Fin n),
            ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V) := by
        intro S hS
        have hlt : Module.finrank k S.toSubmodule < Module.finrank k V :=
          Submodule.finrank_lt (fun H => hS (Subrepresentation.ext H))
        obtain ⟨n, b, hb⟩ := ih _ (by omega) G S.toSubmodule S.toRepresentation rfl hG hcard
        refine ⟨n, b, fun g i => ?_⟩
        obtain ⟨j, c, hj⟩ := hb g i
        exact ⟨j, c, congrArg Subtype.val hj⟩
      refine exists_monomial_basis_of_isCompl ρ _ _ hcompl (hsub U hU1) (hsub U' ?_)
      rintro rfl
      exact hU0 (by simpa using hUU'.inf_eq_bot)
  intro G _ _ V _ _ _ ρ _ hG hc
  exact key _ G V ρ rfl hG hc

end GlobalTheory.CuspGL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsMonomialBasisAbelianByPrimePowerStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.exists_monomial_basis_abelianByPrimePower : ∀ (k : Type) [Field k] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k], AbByP G → (Nat.card G : k) ≠ 0 → ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n), ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  first | exact @GlobalTheory.CuspGL.exists_monomial_basis_of_abByP | exact GlobalTheory.CuspGL.exists_monomial_basis_of_abByP | (intros; apply GlobalTheory.CuspGL.exists_monomial_basis_of_abByP <;> assumption)
end
end
