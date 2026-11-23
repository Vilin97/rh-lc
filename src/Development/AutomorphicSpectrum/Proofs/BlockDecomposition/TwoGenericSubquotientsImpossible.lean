module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientsEquivOfNotLeStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfNotInCodimOneSubmodule

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RgGuCore

theorem not_inf_le_of_rank_quotient_le_one {V : Type} [AddCommGroup V] [Module ℂ V]
    (T A C : Submodule ℂ V) (hT : Module.rank ℂ (V ⧸ T) ≤ 1)
    (hmod : (A ⊔ C) ⊓ T ≤ A ⊓ T ⊔ C ⊓ T) (hA : ¬ A ≤ T) (hC : ¬ C ≤ T) :
    ¬ A ⊓ C ≤ T := by
  obtain ⟨a, haA, haT⟩ := SetLike.not_le_iff_exists.mp hA
  obtain ⟨c, hcC, hcT⟩ := SetLike.not_le_iff_exists.mp hC
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp hT
  obtain ⟨s, hs⟩ := hv₀ (Submodule.Quotient.mk a)
  obtain ⟨t, ht⟩ := hv₀ (Submodule.Quotient.mk c)
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply haT
    rw [← Submodule.Quotient.mk_eq_zero T, ← hs, zero_smul]
  have hdiff : c - (t * s⁻¹) • a ∈ T := by
    rw [← Submodule.Quotient.mk_eq_zero T, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      ← hs, ← ht, smul_smul, mul_assoc, inv_mul_cancel₀ hs0, mul_one, sub_self]
  have hsum : c - (t * s⁻¹) • a ∈ A ⊔ C :=
    Submodule.sub_mem _ (Submodule.mem_sup_right hcC)
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ haA))
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (hmod (Submodule.mem_inf.mpr ⟨hsum, hdiff⟩))
  rw [Submodule.mem_inf] at hx hy
  have hw : c - y = (t * s⁻¹) • a + x := by
    calc c - y = (c - (t * s⁻¹) • a - (x + y)) + (t * s⁻¹) • a + x := by abel
      _ = (t * s⁻¹) • a + x := by rw [hxy, sub_self, zero_add]
  have hwA : c - y ∈ A := hw ▸ Submodule.add_mem _ (Submodule.smul_mem _ _ haA) hx.1
  have hwC : c - y ∈ C := Submodule.sub_mem _ hcC hy.1
  intro h
  apply hcT
  have hwT : c - y ∈ T := h (Submodule.mem_inf.mpr ⟨hwA, hwC⟩)
  simpa using Submodule.add_mem _ hwT hy.2

theorem gen_core_meet {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (T : Submodule ℂ V) (hT : Module.rank ℂ (V ⧸ T) ≤ 1)
    (A C : Subrepresentation ρ)
    (hmod : (A ⊔ C).toSubmodule ⊓ T ≤ A.toSubmodule ⊓ T ⊔ C.toSubmodule ⊓ T)
    (hA : ¬ A.toSubmodule ≤ T) (hC : ¬ C.toSubmodule ≤ T) :
    ¬ (A ⊓ C).toSubmodule ≤ T := by
  rw [Subrepresentation.toSubmodule_sup] at hmod
  rw [Subrepresentation.toSubmodule_inf]
  exact GlobalTheory.CompanionTheory.RgGuCore.not_inf_le_of_rank_quotient_le_one T A.toSubmodule C.toSubmodule hT hmod hA hC

end GlobalTheory.CompanionTheory.RgGuCore
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfNotInCodimOneSubmoduleStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.inf_not_in_codim_one_submodule : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (T : Submodule ℂ V), Module.rank ℂ (V ⧸ T) ≤ 1 → ∀ A C : Subrepresentation ρ, (A ⊔ C).toSubmodule ⊓ T ≤ A.toSubmodule ⊓ T ⊔ C.toSubmodule ⊓ T → ¬ A.toSubmodule ≤ T → ¬ C.toSubmodule ≤ T → ¬ (A ⊓ C).toSubmodule ≤ T := by
  first | exact @GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet | exact GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet | (intros; apply GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfSupEq

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RepSecondIso

theorem subQuot_equiv_of_sup : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (A B E : Subrepresentation ρ), E ≤ A → E ⊔ B = A →
    Nonempty ((subQuot E B).Equiv (subQuot A B)) := by
  intro G V _ _ _ ρ A B E hEA hsup
  have hEA' : E.toSubmodule ≤ A.toSubmodule := fun x hx => hEA hx
  let PE := Submodule.comap E.toSubmodule.subtype B.toSubmodule
  let PA := Submodule.comap A.toSubmodule.subtype B.toSubmodule
  let f : E.toSubmodule →ₗ[ℂ] A.toSubmodule ⧸ PA := PA.mkQ ∘ₗ Submodule.inclusion hEA'
  have hf : PE ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (p := PA) (Submodule.inclusion hEA' x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx
  let φ := PE.liftQ f hf
  have hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Submodule.inclusion hEA' x) :=
    fun _ => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective PE q
    rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hq
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective PA q
    have ha : (a : V) ∈ E.toSubmodule ⊔ B.toSubmodule := by
      rw [← Subrepresentation.toSubmodule_sup, hsup]
      exact a.2
    obtain ⟨e, he, b, hb, hab⟩ := Submodule.mem_sup.mp ha
    refine ⟨Submodule.Quotient.mk ⟨e, he⟩, ?_⟩
    rw [hφ, Submodule.Quotient.eq]
    show e - (a : V) ∈ B.toSubmodule
    have hdiff : e - (a : V) = -b := by
      rw [← hab]
      abel
    rw [hdiff]
    exact B.toSubmodule.neg_mem hb
  let ψ := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  refine ⟨Representation.Equiv.mk' ⟨φ, fun g => ?_⟩ ψ.symm (fun x => ψ.symm_apply_apply x)
    (fun y => ψ.apply_symm_apply y)⟩
  exact Submodule.linearMap_qext _ (LinearMap.ext fun x => rfl)

end GlobalTheory.CompanionTheory.RepSecondIso
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfSupEqStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.subquotient_equiv_of_sup_eq : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (A B E : Subrepresentation ρ), E ≤ A → E ⊔ B = A → Nonempty ((subQuot E B).Equiv (subQuot A B)) := by
  first | exact @GlobalTheory.CompanionTheory.RepSecondIso.subQuot_equiv_of_sup | exact GlobalTheory.CompanionTheory.RepSecondIso.subQuot_equiv_of_sup | (intros; apply GlobalTheory.CompanionTheory.RepSecondIso.subQuot_equiv_of_sup <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupEqOfIrreducibleSubquotient

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenCore

theorem sup_eq_of_isIrreducible_subQuot :
    ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (A B E : Subrepresentation ρ), B ≤ A → (subQuot A B).IsIrreducible → E ≤ A → ¬ E ≤ B →
      E ⊔ B = A := by
  intro G V _ _ _ ρ A B E hBA hirr hEA hEB
  haveI : IsSimpleOrder (Subrepresentation (GlobalTheory.SmGL.subQuot A B)) := hirr
  refine le_antisymm (sup_le hEA hBA) ?_
  let P := Submodule.comap A.toSubmodule.subtype B.toSubmodule
  let S : Submodule ℂ (A.toSubmodule ⧸ P) :=
    Submodule.map P.mkQ (Submodule.comap A.toSubmodule.subtype (E ⊔ B).toSubmodule)
  have hS : ∀ (g : G) ⦃q : A.toSubmodule ⧸ P⦄, q ∈ S →
      GlobalTheory.SmGL.subQuot A B g q ∈ S := by
    intro g q hq
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hq
    exact Submodule.mem_map.mpr
      ⟨⟨ρ g y, A.apply_mem_toSubmodule g y.2⟩, (E ⊔ B).apply_mem_toSubmodule g (v := (y : V)) hy, rfl⟩
  let W : Subrepresentation (GlobalTheory.SmGL.subQuot A B) := ⟨S, hS⟩
  obtain ⟨e, heE, heB⟩ := SetLike.not_le_iff_exists.mp hEB
  have hea : e ∈ A.toSubmodule := hEA heE
  have heEB : e ∈ (E ⊔ B).toSubmodule := (le_sup_left : E ≤ E ⊔ B) heE
  rcases IsSimpleOrder.eq_bot_or_eq_top W with hW | hW
  · exfalso
    let Z : Subrepresentation (GlobalTheory.SmGL.subQuot A B) :=
      ⟨⊥, fun g q hq => by
        rw [Submodule.mem_bot] at hq ⊢
        rw [hq, map_zero]⟩
    have hmem : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ ∈ W := by
      show _ ∈ S
      exact Submodule.mem_map.mpr ⟨⟨e, hea⟩, heEB, rfl⟩
    rw [hW] at hmem
    have hZ : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ ∈ Z := (bot_le : ⊥ ≤ Z) hmem
    have hZ' : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ ∈ (⊥ : Submodule ℂ (A.toSubmodule ⧸ P)) := hZ
    have h0 : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ = 0 := (Submodule.mem_bot ℂ).mp hZ'
    have heP : (⟨e, hea⟩ : A.toSubmodule) ∈ P := (Submodule.Quotient.mk_eq_zero P).mp h0
    exact heB heP
  · intro x hx
    have hxA : x ∈ A.toSubmodule := hx
    let T : Subrepresentation (GlobalTheory.SmGL.subQuot A B) :=
      ⟨⊤, fun _ _ _ => Submodule.mem_top⟩
    have hT : Submodule.Quotient.mk (p := P) ⟨x, hxA⟩ ∈ W := by
      rw [hW]
      exact (le_top : T ≤ ⊤)
        (show Submodule.Quotient.mk (p := P) ⟨x, hxA⟩ ∈ (⊤ : Submodule ℂ (A.toSubmodule ⧸ P)) from
          Submodule.mem_top)
    have hT' : Submodule.Quotient.mk (p := P) ⟨x, hxA⟩ ∈ S := hT
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hT'
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq] at hyx
    have hb : (y : V) - x ∈ B.toSubmodule := hyx
    have hb' : (y : V) - x ∈ (E ⊔ B).toSubmodule := (le_sup_right : B ≤ E ⊔ B) hb
    have hy' : (y : V) ∈ (E ⊔ B).toSubmodule := hy
    have hsub := (E ⊔ B).toSubmodule.sub_mem hy' hb'
    rw [sub_sub_cancel] at hsub
    exact hsub

end GlobalTheory.CompanionTheory.GenCore
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupEqOfIrreducibleSubquotientStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.sup_eq_of_irreducible_subquotient : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (A B E : Subrepresentation ρ), B ≤ A → (subQuot A B).IsIrreducible → E ≤ A → ¬ E ≤ B → E ⊔ B = A := by
  first | exact @GlobalTheory.CompanionTheory.GenCore.sup_eq_of_isIrreducible_subQuot | exact GlobalTheory.CompanionTheory.GenCore.sup_eq_of_isIrreducible_subQuot | (intros; apply GlobalTheory.CompanionTheory.GenCore.sup_eq_of_isIrreducible_subQuot <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoGenericSubquotientsImpossible

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenCoreMain

theorem le_of_not_le_sup {V : Type} [AddCommGroup V] [Module ℂ V] (T A B : Submodule ℂ V)
    (hT : Module.rank ℂ (V ⧸ T) ≤ 1) (hA : ¬ A ≤ B ⊔ T) : B ≤ T := by
  intro b hb
  by_contra hbT
  obtain ⟨a, haA, haBT⟩ := SetLike.not_le_iff_exists.mp hA
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp hT
  obtain ⟨r, hr⟩ := hv₀ (Submodule.Quotient.mk b)
  obtain ⟨s, hs⟩ := hv₀ (Submodule.Quotient.mk a)
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hbT
    rw [zero_smul] at hr
    exact (Submodule.Quotient.mk_eq_zero T).mp hr.symm
  have hmk : Submodule.Quotient.mk (p := T) (a - (s * r⁻¹) • b) = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, ← hr, ← hs, smul_smul,
      mul_assoc, inv_mul_cancel₀ hr0, mul_one, sub_self]
  have ht : a - (s * r⁻¹) • b ∈ T := (Submodule.Quotient.mk_eq_zero T).mp hmk
  apply haBT
  have : a = (s * r⁻¹) • b + (a - (s * r⁻¹) • b) := by abel
  rw [this]
  exact Submodule.add_mem_sup (B.smul_mem _ hb) ht

theorem nonempty_equiv_of_generic {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (T : Submodule ℂ V) (hT : Module.rank ℂ (V ⧸ T) ≤ 1)
    (hsup : ∀ X Y : Subrepresentation ρ,
      (X ⊔ Y).toSubmodule ⊓ T ≤ X.toSubmodule ⊓ T ⊔ Y.toSubmodule ⊓ T)
    (A B C D : Subrepresentation ρ) (hBA : B ≤ A) (hDC : D ≤ C)
    (hAB : (subQuot A B).IsIrreducible) (hCD : (subQuot C D).IsIrreducible)
    (hA : ¬ A.toSubmodule ≤ B.toSubmodule ⊔ T) (hC : ¬ C.toSubmodule ≤ D.toSubmodule ⊔ T) :
    Nonempty ((subQuot A B).Equiv (subQuot C D)) := by
  have hBT : B.toSubmodule ≤ T := le_of_not_le_sup T _ _ hT hA
  have hDT : D.toSubmodule ≤ T := le_of_not_le_sup T _ _ hT hC
  have hAT : ¬ A.toSubmodule ≤ T := fun h => hA (h.trans le_sup_right)
  have hCT : ¬ C.toSubmodule ≤ T := fun h => hC (h.trans le_sup_right)
  have hET : ¬ (A ⊓ C).toSubmodule ≤ T := GlobalTheory.T.inf_not_in_codim_one_submodule ρ T hT A C (hsup A C) hAT hCT
  have hEA : A ⊓ C ≤ A := inf_le_left
  have hEC : A ⊓ C ≤ C := inf_le_right
  have hEB : ¬ A ⊓ C ≤ B := fun h => hET (le_trans h hBT)
  have hED : ¬ A ⊓ C ≤ D := fun h => hET (le_trans h hDT)
  have hfillB := GlobalTheory.T.sup_eq_of_irreducible_subquotient ρ A B (A ⊓ C) hBA hAB hEA hEB
  have hfillD := GlobalTheory.T.sup_eq_of_irreducible_subquotient ρ C D (A ⊓ C) hDC hCD hEC hED
  obtain ⟨e₁⟩ := GlobalTheory.T.subquotient_equiv_of_sup_eq ρ A B (A ⊓ C) hEA hfillB
  obtain ⟨e₂⟩ := GlobalTheory.T.subquotient_equiv_of_sup_eq ρ C D (A ⊓ C) hEC hfillD
  have hiB : (subQuot (A ⊓ C) B).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₁.symm hAB
  have hiD : (subQuot (A ⊓ C) D).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₂.symm hCD
  have hnot : ¬ A ⊓ C ≤ (A ⊓ C) ⊓ B ⊔ (A ⊓ C) ⊓ D := by
    intro h
    apply hET
    have h3 : ((A ⊓ C) ⊓ B ⊔ (A ⊓ C) ⊓ D).toSubmodule ≤ T := by
      rw [Subrepresentation.toSubmodule_sup, Subrepresentation.toSubmodule_inf,
        Subrepresentation.toSubmodule_inf]
      exact sup_le (inf_le_right.trans hBT) (inf_le_right.trans hDT)
    exact (fun v hv => h3 (h hv) : (A ⊓ C).toSubmodule ≤ T)
  obtain ⟨e₃⟩ := GlobalTheory.T.irreducible_subquotients_equiv_of_not_le ρ (A ⊓ C) B D hiB hiD hnot
  exact ⟨(e₁.symm.trans e₃).trans e₂⟩

end GlobalTheory.CompanionTheory.GenCoreMain
end
end
