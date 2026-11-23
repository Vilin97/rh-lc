module

public import Formalism.LocalToGlobal.Columns.ToHLat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Index
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLevelPrincipalFirstBlockIndexEqCardStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFormsOfToH
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitMassFormulaFiniteIndexSubgroup

section

@[expose] public section

open MulAction

namespace GlobalTheory.OrbitMass

variable {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D]

def toG (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) :
    orbitRel.Quotient H D → orbitRel.Quotient G D :=
  Quotient.map' id (fun a b hab => by
    change a ∈ orbit H b at hab
    change a ∈ orbit G b
    obtain ⟨h, rfl⟩ := hab
    exact ⟨ι h, hc h b⟩)

def toCoset (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) :
    G ⧸ ι.range → orbitRel.Quotient H D :=
  fun ω => Quotient.liftOn' ω (fun g => (Quotient.mk'' (g⁻¹ • x) : orbitRel.Quotient H D)) (by
    intro g₁ g₂ hg
    rw [QuotientGroup.leftRel_apply, MonoidHom.mem_range] at hg
    obtain ⟨h, hh⟩ := hg
    apply Quotient.sound'
    change g₁⁻¹ • x ∈ orbit H (g₂⁻¹ • x)
    refine ⟨h, ?_⟩
    change h • g₂⁻¹ • x = g₁⁻¹ • x
    rw [← hc, smul_smul, hh, mul_inv_cancel_right])

theorem toCoset_mk (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (g : G) :
    toCoset ι hc x (g : G ⧸ ι.range) = Quotient.mk'' (g⁻¹ • x) := rfl

theorem toCoset_eq_iff (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (a g : G) :
    toCoset ι hc x (g : G ⧸ ι.range) = Quotient.mk'' (a⁻¹ • x) ↔
      (g : G ⧸ ι.range) ∈ orbit (stabilizer G x) (a : G ⧸ ι.range) := by
  rw [toCoset_mk, Quotient.eq'']
  change g⁻¹ • x ∈ orbit H (a⁻¹ • x) ↔ _
  rw [mem_orbit_iff, mem_orbit_iff]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨⟨g * ι h * a⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, mul_smul, hc, hh, smul_inv_smul]
    · change ((g * ι h * a⁻¹ : G) • (a : G ⧸ ι.range)) = g
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      exact ⟨h⁻¹, by simp [mul_assoc]⟩
  · rintro ⟨⟨s, hs⟩, hsa⟩
    change ((s : G) • (a : G ⧸ ι.range)) = g at hsa
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, MonoidHom.mem_range] at hsa
    obtain ⟨k, hk⟩ := hsa
    have hg : g = s * a * ι k := by rw [hk, smul_eq_mul, mul_inv_cancel_left]
    subst hg
    have hs' : s⁻¹ • x = x := by rw [inv_smul_eq_iff]; exact (mem_stabilizer_iff.mp hs).symm
    refine ⟨k⁻¹, ?_⟩
    rw [← hc, map_inv, mul_inv_rev, mul_inv_rev, mul_smul, mul_smul, hs']

theorem card_stab (ι : H →* G) (hinj : Function.Injective ι)
    (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (a : G) :
    Nat.card (stabilizer (stabilizer G x) (a : G ⧸ ι.range)) =
      Nat.card (stabilizer H (a⁻¹ • x)) := by
  symm
  refine Nat.card_eq_of_bijective
    (fun h => ⟨⟨a * ι h.1 * a⁻¹, by
      rw [mem_stabilizer_iff, mul_smul, mul_smul, hc, mem_stabilizer_iff.mp h.2, smul_inv_smul]⟩,
      by
        rw [mem_stabilizer_iff]
        change ((a * ι h.1 * a⁻¹ : G) • (a : G ⧸ ι.range)) = a
        rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
        exact ⟨h.1⁻¹, by simp [mul_assoc]⟩⟩) ⟨?_, ?_⟩
  · intro h₁ h₂ he
    have e : a * ι h₁.1 * a⁻¹ = a * ι h₂.1 * a⁻¹ := congrArg (fun s => ((s.1 : stabilizer G x) : G)) he
    exact Subtype.ext (hinj (mul_left_cancel (mul_right_cancel e)))
  · rintro ⟨⟨s, hs⟩, hsa⟩
    rw [mem_stabilizer_iff] at hsa
    change ((s : G) • (a : G ⧸ ι.range)) = a at hsa
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, MonoidHom.mem_range] at hsa
    obtain ⟨k, hk⟩ := hsa
    have e : ι k⁻¹ = a⁻¹ * s * a := by
      rw [map_inv, hk, smul_eq_mul]; group
    refine ⟨⟨k⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, ← hc, e, mul_smul, mul_smul, smul_inv_smul, mem_stabilizer_iff.mp hs]
    · apply Subtype.ext; apply Subtype.ext
      change a * ι k⁻¹ * a⁻¹ = s
      rw [e]; group

theorem toG_mk (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (y : D) :
    toG ι hc (Quotient.mk'' y) = Quotient.mk'' y := rfl

theorem sum_fiber (ι : H →* G) (hinj : Function.Injective ι)
    (hc : ∀ (h : H) (d : D), ι h • d = h • d) [ι.range.FiniteIndex]
    (c' : orbitRel.Quotient G D) [Finite (stabilizer G (Quotient.out c'))]
    [Fintype (orbitRel.Quotient H D)] [DecidableEq (orbitRel.Quotient G D)] :
    ∑ c ∈ Finset.univ.filter (fun c => toG ι hc c = c'),
        ((Nat.card (stabilizer H (Quotient.out c)) : ℂ))⁻¹
      = (ι.range.index : ℂ) / Nat.card (stabilizer G (Quotient.out c')) := by
  classical
  set x := Quotient.out c' with hx
  haveI : Fintype (G ⧸ ι.range) := Fintype.ofFinite _
  have hS0 : 0 < Nat.card (stabilizer G x) := Nat.card_pos
  have hidx : (ι.range.index : ℂ) / Nat.card (stabilizer G x) =
      ∑ _ω : G ⧸ ι.range, ((Nat.card (stabilizer G x) : ℂ))⁻¹ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.index_eq_card,
      Nat.card_eq_fintype_card, div_eq_mul_inv]
  rw [hidx, ← Finset.sum_fiberwise Finset.univ (toCoset ι hc x), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  split_ifs with hcx
  · have hmem : Quotient.out c ∈ orbit G x := by
      have h1 : (Quotient.mk'' (Quotient.out c) : orbitRel.Quotient G D) = Quotient.mk'' x := by
        rw [← toG_mk ι hc, Quotient.out_eq', hcx, hx, Quotient.out_eq']
      exact Quotient.exact' h1
    obtain ⟨b, hb⟩ := hmem
    have hy : (b⁻¹)⁻¹ • x = Quotient.out c := by rw [inv_inv]; exact hb
    have hfib : (Finset.univ.filter (fun ω => toCoset ι hc x ω = c)) =
        (orbit (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range)).toFinset := by
      ext ω
      induction ω using QuotientGroup.induction_on with
      | H g =>
        rw [Finset.mem_filter, Set.mem_toFinset, ← toCoset_eq_iff ι hc x b⁻¹ g, hy,
          Quotient.out_eq']
        simp
    have hcard := Subgroup.card_mul_index (stabilizer (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range))
    rw [index_stabilizer, card_stab ι hinj hc x b⁻¹, hy] at hcard
    rw [hfib, ← Set.ncard_eq_toFinset_card']
    have hm0 : Nat.card (stabilizer H (Quotient.out c)) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hcard; omega
    have hn0 : (orbit (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range)).ncard ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hcard; omega
    rw [← hcard]
    push_cast
    field_simp
  · rw [Finset.card_eq_zero.mpr, Nat.cast_zero, zero_mul]
    rw [Finset.filter_eq_empty_iff]
    intro ω _ hω
    apply hcx
    rw [← hω]
    induction ω using QuotientGroup.induction_on with
    | H g =>
      rw [toCoset_mk, toG_mk, hx]
      conv_rhs => rw [← Quotient.out_eq' c']
      exact Quotient.sound' ⟨g⁻¹, rfl⟩

theorem mass_formula : ∀ {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D] (ι : H →* G), Function.Injective ι → (∀ (h : H) (d : D), ι h • d = h • d) → ι.range.FiniteIndex → (∀ d : D, Finite (MulAction.stabilizer G d)) → ∀ [Fintype (MulAction.orbitRel.Quotient G D)] [Fintype (MulAction.orbitRel.Quotient H D)] (f : D → ℂ), (∀ (g : G) (d : D), f (g • d) = f d) → ∑ c : MulAction.orbitRel.Quotient H D, ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) = (ι.range.index : ℂ) * ∑ c : MulAction.orbitRel.Quotient G D, ((Nat.card (MulAction.stabilizer G (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) := by
  intro G H D _ _ _ _ ι hinj hc hfi hfin _ _ f hf
  classical
  rw [← Finset.sum_fiberwise Finset.univ (toG ι hc)
    (fun c => ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  have hconst : ∀ c ∈ Finset.univ.filter (fun c => toG ι hc c = c'),
      ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) =
      ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c') := by
    intro c hc'
    rw [Finset.mem_filter] at hc'
    have h1 : (Quotient.mk'' (Quotient.out c) : orbitRel.Quotient G D) = Quotient.mk'' (Quotient.out c') := by
      rw [← toG_mk ι hc, Quotient.out_eq', hc'.2, Quotient.out_eq']
    obtain ⟨g, hg⟩ := (Quotient.exact' h1 : Quotient.out c ∈ orbit G (Quotient.out c'))
    rw [← hg]
    change _ * f (g • Quotient.out c') = _
    rw [hf]
  haveI := hfin (Quotient.out c')
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul, sum_fiber ι hinj hc c', div_eq_mul_inv, mul_assoc]

end GlobalTheory.OrbitMass
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitMassFormulaFiniteIndexSubgroupStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.orbit_mass_formula_finiteIndex_subgroup : ∀ {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D] (ι : H →* G), Function.Injective ι → (∀ (h : H) (d : D), ι h • d = h • d) → ι.range.FiniteIndex → (∀ d : D, Finite (MulAction.stabilizer G d)) → ∀ [Fintype (MulAction.orbitRel.Quotient G D)] [Fintype (MulAction.orbitRel.Quotient H D)] (f : D → ℂ), (∀ (g : G) (d : D), f (g • d) = f d) → ∑ c : MulAction.orbitRel.Quotient H D, ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) = (ι.range.index : ℂ) * ∑ c : MulAction.orbitRel.Quotient G D, ((Nat.card (MulAction.stabilizer G (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) := by
  first | exact @GlobalTheory.OrbitMass.mass_formula | exact GlobalTheory.OrbitMass.mass_formula | (intros; apply GlobalTheory.OrbitMass.mass_formula <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumPrincipalLevelEqCardMulClassSum

section

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem change_of_level_classSum : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (v : InfinitePlace X.K) (F' : (mtildeKGSD W Ch sel mu).EqFun), F'.1 ∈ (mtildeGSD W Ch sel mu P).EqFun → (mtildeKGSD W Ch sel mu).ipAt (mtildeKOk W Ch sel mu hX) v F'.1 F'.1 = (Nat.card P.grp : ℂ) * (mtildeGSD W Ch sel mu P).ipAt (mtildeOk W Ch sel mu hX P) v F'.1 F'.1 := by
  intro X Pr R W Ch sel S mu P hX v F' hF
  obtain ⟨ι, hinj, hact, hidx⟩ := GlobalTheory.T.rowLevel_principal_firstBlock_index_eq_card W Ch sel mu P
  have hK := mtildeKOk W Ch sel mu hX
  have hP := mtildeOk W Ch sel mu hX P
  have hf : ∀ (g : (mtildeGSD W Ch sel mu P).G) (d : (mtildeGSD W Ch sel mu P).D),
      (mtildeGSD W Ch sel mu P).pairAt v (F'.1 (g • d)) (F'.1 (g • d)) =
      (mtildeGSD W Ch sel mu P).pairAt v (F'.1 d) (F'.1 d) := by
    intro g d
    rw [hF g d]
    exact GlobalTheory.PeriodOnStep.pairAt_rho v _ hP (GlobalTheory.PeriodOnStep.row_act_rat W Ch sel mu P hX) g _
  have hfi : ι.range.FiniteIndex := ⟨by rw [hidx]; exact Nat.card_pos.ne'⟩
  have key := @GlobalTheory.T.orbit_mass_formula_finiteIndex_subgroup (mtildeGSD W Ch sel mu P).G (mtildeKGSD W Ch sel mu).G (mtildeGSD W Ch sel mu P).D _ _ _ _ ι hinj hact hfi
    hP.fin_stab (mtildeOk W Ch sel mu hX P).fintypeCl (mtildeKOk W Ch sel mu hX).fintypeCl
    (fun d => (mtildeGSD W Ch sel mu P).pairAt v (F'.1 d) (F'.1 d)) hf
  rw [hidx] at key
  unfold GSD.ipAt
  refine Eq.trans ?_ (key.trans ?_)
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [@Nat.card_eq_fintype_card _ ((mtildeKOk W Ch sel mu hX).fintypeStab _)]
    rfl
  · congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [@Nat.card_eq_fintype_card _ ((mtildeOk W Ch sel mu hX P).fintypeStab _)]
    rfl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumPrincipalLevelEqCardMulClassSumStatement

section

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.classSum_principalLevel_eq_card_mul_classSum : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (v : InfinitePlace X.K) (F' : (mtildeKGSD W Ch sel mu).EqFun), F'.1 ∈ (mtildeGSD W Ch sel mu P).EqFun → (mtildeKGSD W Ch sel mu).ipAt (mtildeKOk W Ch sel mu hX) v F'.1 F'.1 = (Nat.card P.grp : ℂ) * (mtildeGSD W Ch sel mu P).ipAt (mtildeOk W Ch sel mu hX P) v F'.1 F'.1 := by
  first | exact @GlobalTheory.change_of_level_classSum | exact GlobalTheory.change_of_level_classSum | (intros; apply GlobalTheory.change_of_level_classSum <;> assumption)
end
end
