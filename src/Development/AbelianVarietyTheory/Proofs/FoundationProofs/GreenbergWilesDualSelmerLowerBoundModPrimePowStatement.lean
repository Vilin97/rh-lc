module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ArchimedeanInvariantsCardStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommutatorDetNonzero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardOrdinaryLocalConditionModPrimePowLeConstMulStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerClassesGiveNoncohomologousCochainsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerModPrimePowInjectsResidualSelmerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedH1CardInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualEvalBidualApply

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGaloisInvariantsOrdinaryRankTwoModPowBounded

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwCard

variable {l : ℕ} [Fact l.Prime]

theorem natCast_not_isUnit (c : Coef l) : ¬ IsUnit ((l : ℕ) : c.O) := by
  rintro ⟨u, hu⟩
  have h2 : ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ ≤ 1 := CupCob.norm_le_one_of_mem c ((u⁻¹ : c.Oˣ) : c.O).2
  have h3 : (((u : c.Oˣ) : c.O) : Qbar l) * (((u⁻¹ : c.Oˣ) : c.O) : Qbar l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  have hu' : (((u : c.Oˣ) : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := by rw [hu]; simp
  rw [hu'] at h3
  have hl : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℕ) : ℚ_[l]) := by simp
    rw [e, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have := congrArg norm h3
  rw [norm_mul, norm_one] at this
  have : ‖((l : ℕ) : Qbar l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hl
  linarith

theorem exists_dvd_pow (c : Coef l) {d : c.O} (hd : d ≠ 0) : ∃ k : ℕ, d ∣ ((l : ℕ) : c.O) ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
  refine ⟨k, ?_⟩
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : c.O => (x : Qbar l)) h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h'
    exact (Fact.out : l.Prime).ne_zero h'
  have hl : ϖ ∣ ((l : ℕ) : c.O) := by
    obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hϖ
    rcases m with _ | m
    · exact absurd (hm.isUnit_iff.2 (by simp)) (natCast_not_isUnit c)
    · exact (dvd_pow_self ϖ (Nat.succ_ne_zero m)).trans hm.symm.dvd
  exact hk.dvd.trans (pow_dvd_pow_of_dvd hl k)

end GlobalTheory.Ord2.GwCard

noncomputable section

namespace GlobalTheory.Ord2.GwCard

variable {l : ℕ} [Fact l.Prime]

theorem card_ker_eq_index {R : Type} [Ring R] [Finite R] (x : R) :
    Nat.card (AddMonoidHom.mulLeft x).ker = (AddMonoidHom.mulLeft x).range.index := by
  set f := AddMonoidHom.mulLeft x
  have h1 := AddSubgroup.card_mul_index f.ker
  have h2 := AddSubgroup.card_mul_index f.range
  have h3 : f.ker.index = Nat.card f.range := by
    rw [AddSubgroup.index]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  rw [h3] at h1
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have := h1.trans h2.symm
  rw [mul_comm] at this
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem exists_card_ker_pow_le (c : Coef l) (k : ℕ) :
    ∃ B : ℕ, ∀ n : ℕ, Nat.card (AddMonoidHom.mulLeft (((l : ℕ) : Qn c n) ^ k)).ker ≤ B := by
  obtain ⟨g, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := c.O)
  refine ⟨Nat.card (Fin g → ZMod (l ^ k)), fun n => ?_⟩
  rw [card_ker_eq_index, AddSubgroup.index]
  set H := (AddMonoidHom.mulLeft (((l : ℕ) : Qn c n) ^ k)).range
  refine Nat.card_le_card_of_surjective
    (fun z : Fin g → ZMod (l ^ k) => (QuotientAddGroup.mk (∑ i, (z i).val • red c n (s i)) : Qn c n ⧸ H)) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := red_surjective c n y
  have hx : x ∈ Submodule.span ℤ_[l] (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).1 hx
  refine ⟨fun i => PadicInt.toZModPow k (a i), ?_⟩
  simp only

  rw [QuotientAddGroup.eq, ← ha, map_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[l], a i - (PadicInt.toZModPow k (a i)).val = (l : ℤ_[l]) ^ k * w := by
    have hm : a i - ((PadicInt.toZModPow k (a i)).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hm
    exact ⟨w, by rw [← hw, mul_comm]⟩
  refine ⟨red c n (w • s i), ?_⟩
  have e1 : (PadicInt.toZModPow k (a i)).val • red c n (s i) = red c n ((((PadicInt.toZModPow k (a i)).val : ℕ) : ℤ_[l]) • s i) := by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul]
  rw [e1, ← map_neg, ← map_add (f := _), ← neg_smul, ← add_smul, neg_add_eq_sub, hw, mul_smul]
  simp only [AddMonoidHom.coe_mulLeft]
  rw [← map_natCast (red c n), ← map_pow, ← map_mul]
  congr 1
  rw [← Nat.cast_pow (α := ℤ_[l]), Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_pow]

end GlobalTheory.Ord2.GwCard

namespace GlobalTheory.Ord2.GwCard

theorem exists_card_H0_rhoS_le : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l)
    (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1),
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Nat.card (H0 (rhoS c n W hint S hN)) ≤ C := by
  intro l _ Ω _ _ _ e S A W hW c hint hN
  obtain ⟨φ, -, hφ⟩ := GlobalTheory.Ord2.commutator_H0_has_no_eigenvalue_one (l := l) (Ω := Ω) (e := e) (S := S) (A := A) (W := W) hW
  let M : Matrix (Fin 2) (Fin 2) c.O := Matrix.of fun i j => ⟨mat W φ i j, hint φ i j⟩
  have hM : (c.O.val : c.O →+* Qbar l).mapMatrix (M - 1) = mat W φ - 1 := by
    rw [map_sub, map_one]
    congr 1
  have hd : (M - 1).det ≠ 0 := by
    intro h
    apply hφ
    rw [← hM, ← RingHom.map_det, h, map_zero]
  obtain ⟨k, y, hy⟩ := exists_dvd_pow c hd
  obtain ⟨B, hB⟩ := exists_card_ker_pow_le c k
  refine ⟨B ^ 2, fun n _ => ?_⟩
  set K := (AddMonoidHom.mulLeft (((l : ℕ) : Qn c n) ^ k)).ker
  have hred : (red c n).mapMatrix (M - 1) = matQ c n W hint φ - 1 := by
    rw [map_sub, map_one]
    congr 1
  have hmem : ∀ m ∈ H0 (rhoS c n W hint S hN), ∀ i, m i ∈ K := by
    intro m hm i
    have h1 : matQ c n W hint φ *ᵥ m = m := (mem_riemannRochSpace_iff_regularAt_everywhere _ m).1 hm (toGS Ω (S : Set Pl) φ)
    have h2 : (matQ c n W hint φ - 1) *ᵥ m = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, h1, sub_self]
    have h3 : (matQ c n W hint φ - 1).det • m = 0 := by
      rw [← Matrix.one_mulVec m, ← Matrix.smul_mulVec, ← Matrix.adjugate_mul, ← Matrix.mulVec_mulVec, h2,
        Matrix.mulVec_zero]
    have h4 : red c n (M - 1).det * m i = 0 := by
      rw [RingHom.map_det, hred]
      have := congrFun h3 i
      simpa using this
    show ((l : ℕ) : Qn c n) ^ k * m i = 0
    rw [← map_natCast (red c n), ← map_pow, hy, map_mul, mul_comm (red c n _), mul_assoc, h4, mul_zero]
  let F : H0 (rhoS c n W hint S hN) → (Fin 2 → K) := fun m i => ⟨m.1 i, hmem m.1 m.2 i⟩
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hab i)
  calc Nat.card (H0 (rhoS c n W hint S hN)) ≤ Nat.card (Fin 2 → K) := Nat.card_le_card_of_injective F hF
    _ = Nat.card K ^ 2 := by simp [Nat.card_fun]
    _ ≤ B ^ 2 := Nat.pow_le_pow_left (hB n) 2

end GlobalTheory.Ord2.GwCard
end
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGaloisInvariantsOrdinaryRankTwoModPowBoundedStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix


theorem _root_.GlobalTheory.T.card_galoisInvariants_ordinaryRankTwo_mod_pow_bounded : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1), ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Nat.card (H0 (rhoS c n W hint S hN)) ≤ C := by
  first | exact @GlobalTheory.Ord2.GwCard.exists_card_H0_rhoS_le | exact GlobalTheory.Ord2.GwCard.exists_card_H0_rhoS_le | (intros; apply GlobalTheory.Ord2.GwCard.exists_card_H0_rhoS_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergWilesDualSelmerLowerBoundModPrimePow

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwIneq

theorem exists_cc (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] :
    ∃ cc : InfinitePlace ℚ → G ℚ Ω, ∀ w, w.IsReal → IsCCAt w (cc w) := by
  have h : ∀ w : InfinitePlace ℚ, ∃ c : G ℚ Ω, w.IsReal → IsCCAt w c := fun w => by
    by_cases hw : w.IsReal
    · haveI : Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree
      haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
      haveI : IsGalois ℚ Ω := {}
      letI : Algebra ℚ ℂ := w.embedding.toAlgebra
      let j : Ω →ₐ[ℚ] ℂ := (by
        refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
        solve_by_elim* (maxDepth := 2) only [*,
          @_root_.DivisionSemiring.to_moduleIsTorsionFree,
          @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
      have hr : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.1 hw
      let cj : ℂ →ₐ[ℚ] ℂ := { starRingEnd ℂ with commutes' := fun x => RingHom.congr_fun hr x }
      letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
      haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
      refine ⟨(cj.comp j).restrictNormal' Ω, fun _ => ⟨j.toRingHom, fun x => ?_, ?_⟩⟩
      · exact AlgHom.restrictNormal_commutes (cj.comp j) Ω x
      · rw [show j.toRingHom.comp (algebraMap ℚ Ω) = w.embedding from RingHom.ext fun x => j.commutes x]
        exact w.mk_embedding
    · exact ⟨1, fun h => absurd h hw⟩
  choose cc hcc using h
  exact ⟨cc, hcc⟩

theorem gw_ineq : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (y : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A W (y i)) → (∀ i j, i ≠ j → ¬ Cob1 c n W ⊤ (y i - y j)) → ∃ (N' : ℕ) (z : Fin N' → G ℚ Ω → Fin 2 → Qbar l), N ≤ C * N' ∧ (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) ∧ ∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j) := by
  classical
  intro hL l _ Ω _ _ _ e S A W hW c hint
  have hN := kills_NS hW
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.card_galoisInvariants_ordinaryRankTwo_mod_pow_bounded l Ω e S A W hW c hint hN
  obtain ⟨CA, hCA⟩ := GlobalTheory.T.card_ordinaryLocalConditionModPrimePow_le_const_mul hL l Ω e S A W hW c hint hN
  refine ⟨C0 * CA, fun n hn N y hy hyd => ?_⟩
  have hn0 : 0 < n := hn
  have hS := hW.above
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := n) (S := S) hS
  obtain ⟨cc, hcc⟩ := exists_cc Ω
  have hρ : ReciprocityTheory.Gal.ContAction (rhoS c n W hint S hN) := contAction_rhoS c n W hint S hN hW.cont
  have hgw := hL.gw ℚ Ω l n (Mn c n) S (rhoS c n W hint S hN) hn0 hW.l_odd hS hρ μ hμ (Av A S)
    (isPlaceOver_Av A S) cc hcc (Lc c n W hint S hN A)
  have hρd : ReciprocityTheory.Gal.ContAction (twDual μ (rhoS c n W hint S hN)) :=
    GlobalTheory.DualSide.contAction_twDual (GlobalTheory.Published.PoitouTate.contAction_charRep hμ) hρ
  haveI : Finite (TDual (ZMod (l ^ n)) (Mn c n)) := GlobalTheory.DualSide.finite_TDual
  haveI : Finite (H1 (rhoS c n W hint S hN)) := (hL.gf ℚ Ω l n (Mn c n) S _ hn0 hS hρ).2.1
  haveI : Finite (H1 (twDual μ (rhoS c n W hint S hN))) :=
    (hL.gf ℚ Ω l n (TDual (ZMod (l ^ n)) (Mn c n)) S _ hn0 hS hρd).2.1

  obtain ⟨v0, hA0, hl0⟩ := hW.atL
  let vA : S := ⟨v0, hS v0 hl0⟩
  have huniq : ∀ v w : Pl, IsPlaceOver A v → IsPlaceOver A w → v = w := fun v w hv hw =>
    HeightOneSpectrum.ext (Ideal.ext fun x => (hv x).symm.trans (hw x))
  have hLv : ∀ v : S, v ≠ vA → Nat.card (Lc c n W hint S hN A v) =
      Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))) := by
    intro v hv
    have hnp : ¬ IsPlaceOver A v.1 := fun h => hv (Subtype.ext (huniq _ _ h hA0))
    have e1 : Lc c n W hint S hN A v = H1ur ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))
        ((Ine (F := ℚ) (Av A S v)).subgroupOf (Dec (F := ℚ) (Av A S v))) := if_neg hnp
    rw [e1]
    exact GlobalTheory.Ord2.UrCard.card_unramified_h1_eq_card_h0 ℚ Ω l n (Mn c n) (Av A S v) v.1 _
      (hρ.comp' (continuous_locFam S (Av A S) v)) (isPlaceOver_Av A S v)
  have harch := GlobalTheory.T.archimedean_invariants_card l Ω e S A W hW c hint hN n hn cc hcc
  rw [harch, ← Finset.mul_prod_erase _ _ (Finset.mem_univ vA),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ vA),
    Finset.prod_congr rfl fun v hv => hLv v (Finset.ne_of_mem_erase hv)] at hgw
  have hLA := hCA n hn vA hA0
  have hH0 := hC0 n hn
  have hP : 0 < ∏ v ∈ Finset.univ.erase vA, Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))) :=
    Finset.prod_pos fun v _ => Nat.card_pos
  have hq : 0 < Nat.card (Qn c n) := Nat.card_pos
  have h1d : 1 ≤ Nat.card (H0 (twDual μ (rhoS c n W hint S hN))) := Nat.card_pos
  have h1A : 1 ≤ Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) vA))) := Nat.card_pos
  set P := ∏ v ∈ Finset.univ.erase vA, Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v)))
  have hsel : Nat.card (SelG c n W hint S hN A) ≤ C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ) := by
    have key : Nat.card (SelG c n W hint S hN A) * (Nat.card (Qn c n) * P) ≤
        (C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ)) * (Nat.card (Qn c n) * P) := by
      calc Nat.card (SelG c n W hint S hN A) * (Nat.card (Qn c n) * P)
          = Nat.card (SelG c n W hint S hN A) * 1 * (1 * P) * Nat.card (Qn c n) := by ring
        _ ≤ Nat.card (SelG c n W hint S hN A) * Nat.card (H0 (twDual μ (rhoS c n W hint S hN))) *
            (Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) vA))) * P) * Nat.card (Qn c n) := by
          gcongr
        _ = Nat.card (SelD c n W hint S hN A hW.cont μ) * Nat.card (H0 (rhoS c n W hint S hN)) *
            (Nat.card (Lc c n W hint S hN A vA) * P) := hgw
        _ ≤ Nat.card (SelD c n W hint S hN A hW.cont μ) * C0 * (CA * Nat.card (Qn c n) * P) := by
          gcongr
        _ = (C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ)) * (Nat.card (Qn c n) * P) := by ring
    exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hq hP)

  obtain ⟨cls, hcls, hinj⟩ := GlobalTheory.T.ordinarySelmerModPrimePow_injects_residualSelmer l Ω e S A W hW c hint hN n hn
  have hN1 : N ≤ Nat.card (SelG c n W hint S hN A) := by
    let f : Fin N → SelG c n W hint S hN A := fun i => ⟨cls (y i), hcls _ (hy i)⟩
    have hf : Function.Injective f := by
      intro i j hij
      by_contra hne
      exact hyd i j hne (hinj _ _ (hy i) (hy j) (congrArg Subtype.val hij))
    simpa using Nat.card_le_card_of_injective f hf

  obtain ⟨z, hz, hzd⟩ := GlobalTheory.T.dualSelmer_classes_give_noncohomologous_cochains hL l Ω e S A W hW c hint hN n hn μ hμ
  let eqv := Finite.equivFin (SelD c n W hint S hN A hW.cont μ)
  refine ⟨Nat.card (SelD c n W hint S hN A hW.cont μ), fun i => z (eqv.symm i), ?_, fun i => hz _, ?_⟩
  · exact hN1.trans hsel
  · intro i j hij
    exact hzd _ _ (fun h => hij (eqv.symm.injective h))

end GlobalTheory.Ord2.GwIneq
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergWilesDualSelmerLowerBoundModPrimePowStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
theorem _root_.GlobalTheory.T.greenbergWiles_dualSelmer_lower_bound_mod_prime_pow : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (y : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A W (y i)) → (∀ i j, i ≠ j → ¬ Cob1 c n W ⊤ (y i - y j)) → ∃ (N' : ℕ) (z : Fin N' → G ℚ Ω → Fin 2 → Qbar l), N ≤ C * N' ∧ (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) ∧ ∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j) := by
  first | exact @GlobalTheory.Ord2.GwIneq.gw_ineq | exact GlobalTheory.Ord2.GwIneq.gw_ineq | (intros; apply GlobalTheory.Ord2.GwIneq.gw_ineq <;> assumption) | exact @GlobalTheory.Ord2.GwIneq.exists_cc | exact GlobalTheory.Ord2.GwIneq.exists_cc | (intros; apply GlobalTheory.Ord2.GwIneq.exists_cc <;> assumption)
end
end
