module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp

-- Source module: Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReductionUniformizerPoint

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

def ideal (S : Finset ι) : X.IdealSheafData := ⨆ i ∈ S, I i

theorem le_ideal {S : Finset ι} {i : ι} (h : i ∈ S) : I i ≤ ideal I S :=
  le_iSup₂ (f := fun i (_ : i ∈ S) => I i) i h

theorem ideal_mono {S S' : Finset ι} (h : S ⊆ S') : ideal I S ≤ ideal I S' :=
  iSup₂_le fun _ hi => le_ideal I (h hi)

def Y (S : Finset ι) : Scheme.{0} := (ideal I S).subscheme

def Yι (S : Finset ι) : Y I S ⟶ X := (ideal I S).subschemeι

def incl {S S' : Finset ι} (h : S ⊆ S') : Y I S' ⟶ Y I S :=
  Scheme.IdealSheafData.inclusion (ideal_mono I h)

abbrev Idx (ι : Type) (s : ℕ) : Type := {S : Finset ι // S.card = s + 1}

def Ystr (s : ℕ) : Scheme.{0} := ∐ fun S : Idx ι s => Y I S.1

def inj {s : ℕ} (S : Idx ι s) : Y I S.1 ⟶ Ystr I s := Sigma.ι (fun S : Idx ι s => Y I S.1) S

section Face

variable [LinearOrder ι]

def face {s : ℕ} (S : Idx ι (s + 1)) (j : Fin (s + 2)) : Idx ι s :=
  ⟨S.1.erase (S.1.orderEmbOfFin S.2 j), by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), S.2]; rfl⟩

theorem face_subset {s : ℕ} (S : Idx ι (s + 1)) (j : Fin (s + 2)) : (face S j).1 ⊆ S.1 :=
  Finset.erase_subset _ _

def δ (s : ℕ) (j : Fin (s + 2)) : Ystr I (s + 1) ⟶ Ystr I s :=
  Sigma.desc fun S : Idx ι (s + 1) => incl I (face_subset S j) ≫ inj I (face S j)

end Face

end GlobalTheory.Strata

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

section Fibre

variable {O : Type} [CommRing O] (p : X ⟶ Spec (CommRingCat.of O)) (ϖ : O)

end Fibre

section BaseChange

variable {X' : Scheme.{0}} (f : X' ⟶ X)

end BaseChange

theorem nonempty_Ystr {s : ℕ} (S : Idx ι s) (y : Y I S.1) : Nonempty (Ystr I s) := ⟨(inj I S).base y⟩

theorem isEmpty_Ystr {s : ℕ} (h : IsEmpty (Idx ι s)) : IsEmpty (Ystr I s) :=
  ⟨fun x => IsEmpty.false ((Sigma.desc (fun S : Idx ι s => (isEmptyElim S : Y I S.1 ⟶ ∅)) : Ystr I s ⟶ ∅).base x)⟩

theorem nonempty_Y_iff (S : Finset ι) : Nonempty (Y I S) ↔ ((ideal I S).support : Set X).Nonempty := by
  rw [← Set.range_nonempty_iff_nonempty (f := (Yι I S).base)]
  unfold Yι
  rw [← Scheme.IdealSheafData.range_subschemeι]
  rfl

end GlobalTheory.Strata

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

section FibreStr

variable {O : Type} [CommRing O] (p : X ⟶ Spec (CommRingCat.of O)) (ϖ : O)

end FibreStr

section BaseChangeStr

variable {X' : Scheme.{0}} (f : X' ⟶ X)

end BaseChangeStr

end GlobalTheory.Strata

namespace GlobalTheory.Strata.Example

open MvPolynomial

variable (O : Type) [CommRing O] (ϖ : O)

abbrev A : Type := MvPolynomial (Fin 2) O ⧸ Ideal.span {X 0 * X 1 - C ϖ}

def T (k : Fin 2) : A O ϖ := Ideal.Quotient.mk _ (X k)

abbrev XS : Scheme.{0} := Spec (CommRingCat.of (A O ϖ))

def compIdeal (k : Fin 2) : (XS O ϖ).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of (A O ϖ))).inv.hom (T O ϖ k)})

def red : A O ϖ →+* O ⧸ Ideal.span {ϖ} :=
  Ideal.Quotient.lift _ (eval₂Hom (Ideal.Quotient.mk _) (fun _ => 0)) (by
    intro a ha
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    simp [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self])

theorem reduction_uniformizerPoint (k : Fin 2) : red O ϖ (T O ϖ k) = 0 := by simp [red, T]

theorem mem_support_compIdeal (x : XS O ϖ) (k : Fin 2) (hx : T O ϖ k ∈ x.asIdeal) :
    x ∈ ((compIdeal O ϖ k).support : Set (XS O ϖ)) := by
  rw [compIdeal, Scheme.IdealSheafData.coe_support_ofIdealTop, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton,
    basicOpen_eq_of_affine]
  exact fun h' => (PrimeSpectrum.mem_basicOpen (x := (x : PrimeSpectrum (A O ϖ))) _).1 h' hx

theorem isEmpty_Ystr_two : IsEmpty (Ystr (compIdeal O ϖ) 2) :=
  isEmpty_Ystr _ ⟨fun S => by have := S.1.card_le_univ; have h2 := S.2; simp at this; omega⟩

theorem nonempty_Ystr_one (h : ¬ IsUnit ϖ) : Nonempty (Ystr (compIdeal O ϖ) 1) := by
  haveI : Nontrivial (O ⧸ Ideal.span {ϖ}) :=
    Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (O ⧸ Ideal.span {ϖ})
  let x : XS O ϖ := ⟨M.comap (red O ϖ), Ideal.comap_isPrime _ _⟩
  have hx : x ∈ ((ideal (compIdeal O ϖ) Finset.univ).support : Set (XS O ϖ)) := by
    simp only [ideal, Scheme.IdealSheafData.support_iSup, TopologicalSpace.Closeds.coe_iInf, Set.mem_iInter]
    intro k _
    refine mem_support_compIdeal O ϖ x k ?_
    show red O ϖ (T O ϖ k) ∈ M
    rw [reduction_uniformizerPoint]; exact zero_mem _
  obtain ⟨y⟩ := (nonempty_Y_iff (compIdeal O ϖ) Finset.univ).2 ⟨x, hx⟩
  exact nonempty_Ystr (compIdeal O ϖ) (s := 1) ⟨Finset.univ, by simp⟩ y

end GlobalTheory.Strata.Example

namespace GlobalTheory.Strata

theorem orderEmbOfFin_univ_fin {n : ℕ} (h : (Finset.univ : Finset (Fin n)).card = n) :
    ((Finset.univ : Finset (Fin n)).orderEmbOfFin h : Fin n → Fin n) = id :=
  (Finset.orderEmbOfFin_unique h (f := id) (fun _ => Finset.mem_univ _) strictMono_id).symm

end GlobalTheory.Strata
end
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GaloisActionWeightSpectralE1Apply

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime]

def castHQ {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : HQ l E n i ≃ₗ[ℚ_[l]] HQ l E n' i' := by
  subst hn; subst hi; exact LinearEquiv.refl _ _

theorem pullHQ_map_id (E : Spc) (n i : ℤ) : pullHQ l (𝟙 E) n i = LinearMap.id := by
  unfold pullHQ; rw [pullHl_id]; exact LinearMap.baseChange_id

theorem pullHQ_map_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = pullHQ l f n i ∘ₗ pullHQ l g n i := by
  unfold pullHQ; rw [pullHl_comp]; exact LinearMap.baseChange_comp _ _

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime]

def idx (m : ℕ) (a : ℤ) : Finset ℕ := (Finset.range m).filter fun s => -a ≤ (s : ℤ) ∧ a + 2 * (s : ℤ) < m

variable {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

def res (t : ℕ) (n i : ℤ) : HQ l (sch.obj (Ystr J t)) n i →ₗ[ℚ_[l]] HQ l (sch.obj (Ystr J (t + 1))) n i :=
  ∑ j : Fin (t + 2), ((-1 : ℚ_[l]) ^ (j : ℕ)) • pullHQ l (sch.map (δ J t j)) n i

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι]

section Galois

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {V : Scheme.{0}} (p : V ⟶ Spec (CommRingCat.of k))
  (I : ι → V.IdealSheafData)

variable (a b w : ℤ)

end Galois

end GlobalTheory.EtC.WSS
end
end
end
