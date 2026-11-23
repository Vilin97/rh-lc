module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.AlgebraicTheory.StatementA
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Formalism.LocalToGlobal.Divisibility.JetBounds.IsExpansion
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Formalism.LocalToGlobal.Divisibility.ClassSum
import Mathlib.Data.Nat.Choose.Multinomial
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.QuotientMetricDivisors.Complement2Normaliser
import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.NormaliserValuationBound
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

-- Source module: Formalism.LocalToGlobal.ExponentGrids.IntegerShiftClosedExponent

section

@[expose] public section

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols SPer IndefNum IndefCore)
open Formalism.L2.GlobalTheoryTheory (Arith.Cst Arith.Lev Arith.Lev.admitted Arith.sg Arith.elt Arith.eltBar Arith.pOf Arith.EatT)

noncomputable section

namespace Formalism.AtG

section Defs

variable {K : Type} [Field K] [NumberField K]

def PerBd [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} (Dc : DefCols Df) (u : Dc.Mem)
    (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) : Prop :=
  ∀ φ ∈ Nu, ∀ F ∈ Df.Mt t, Dc.Pt u t φ F = 0 ∨ s ≤ (vw w (Dc.Pt u t φ F) : ℝ)

def colRhs {J : Type} (s : Finset J) (g : ℕ) (nn : J → K) (cg : K) (E0 : ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  -(∑ j ∈ s, (vw w (nn j) : ℝ)) + (vw w cg : ℝ) - E0 * (vw w (g : K) : ℝ)


end Defs

end Formalism.AtG
end
end
end

-- Source module: Formalism.LocalToGlobal.AlgebraicTheory.StatementStep

section

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.AlgTh

open Formalism.DivisionValues (vw PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols)
open Formalism.L2.DIV (PathData EmbAt IsExpansion ColsInt RowsInt LastInt UnitsInt StabDvd)
open Formalism.AtG (PerBd colRhs)

def GAt {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} (Dc : DefCols Df) (u : Dc.Mem)
    (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (w : HeightOneSpectrum (𝓞 K)) (g : ℕ) [Fact g.Prime] (pb : K)
    (Dg : Bs.J → ℕ) (Rg : Bs.J → ℝ) : Prop :=
  ∃ (ι : K →+* ℂ_[g]) (X : PathData K g Bs.J (Fin (Dc.a u) → K) (Fin (Df.nV t) → K)) (D : ℕ) (j1 : Bs.J),
    EmbAt w g ι ∧ IsExpansion X ι (Dc.Pt u t) (Nu : Set (Fin (Dc.a u) → K)) (Df.Mt t : Set (Fin (Df.nV t) → K)) ∧
    ColsInt X w (Nu : Set (Fin (Dc.a u) → K)) ∧ RowsInt X w (Df.Mt t : Set (Fin (Df.nV t) → K)) ∧
    LastInt X ∧ UnitsInt X ∧ StabDvd X D j1 ∧ ¬ g ∣ D ∧
    ∀ π j, ‖X.e π j‖ * ‖ι pb‖ ^ (Dg j) * ‖(g : ℂ_[g])‖ ^ (Rg j) ≤ 1

end Formalism.L2.AlgTh
end
end
end

-- Source module: Formalism.LocalToGlobal.ExponentGrids.EntryG

section

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain

namespace Formalism.L2.AtG.EntryG

open Formalism.L2.Col (Fields Sp HomE homAt divLat IsSdLat)
open Formalism.L2.Ker (Amb DVar)
open Formalism.L2.AlgTh (KerStd SplitS JetAtSplit IsQInt GAt)
open Formalism.DivisionValues (vw PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols)
open Formalism.L2.DIV (PathData EmbAt IsExpansion ColsInt RowsInt LastInt UnitsInt StabDvd)
open Formalism.AtG (PerBd colRhs)

section Terms

variable {X : Fields} {p : ℕ} [Fact p.Prime] {a b : ℕ}

structure Term (X : Fields) (p : ℕ) [Fact p.Prime] (a b : ℕ) where

  coef : ℂ_[p]

  scal : X.K

  xi : X.K

  S : Finset (HeightOneSpectrum (𝓞 X.E))

  N : Submodule (𝓞 X.E) (Sp X.E a)

  N' : Submodule (𝓞 X.E) (Sp X.E b)

  c' : ℕ

  x : HomE X.E a b

  m : DVar X.Tau a b →₀ ℕ

def Term.val (A : Amb X) (ι : ℂ ≃+* ℂ_[p]) (T : Term X p a b) : ℂ_[p] :=
  T.coef * ι (A.σ₀ T.scal) * ι (A.σ₀ T.xi) * ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))

def Term.Ok (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (T : Term X p a b) : Prop :=
  ‖T.coef‖ ≤ 1 ∧ ‖ι (A.σ₀ T.scal)‖ ≤ 1 ∧ ‖ι (A.σ₀ T.xi)‖ ≤ ‖(p : ℂ_[p])‖ ^ e ∧
  KerStd A T.N T.N' a₀ b₀ c₀ ha hd lam hlam p ι ∧ IsSdLat T.N ∧ IsSdLat T.N' ∧ A.LaHyp a b T.S ∧ SplitS A T.S p ϖ pE ∧
  0 < T.c' ∧ ¬ p ∣ T.c' ∧ T.x ∈ divLat T.c' (homAt T.S T.N T.N') ∧ T.m.degree = D

def IsEntryG (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (a b : ℕ) (y : ℂ_[p]) : Prop :=
  ∃ (n : ℕ) (T : Fin n → Term X p a b), y = ∑ k, (T k).val A ι ∧ ∀ k, (T k).Ok A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE D e

theorem isEntryG_zero (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (a b : ℕ) : IsEntryG A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE D e a b 0 :=
  ⟨0, Fin.elim0, by simp, fun k => k.elim0⟩

end Terms

section Place

variable {X : Fields}

end Place

section Record

open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Indef

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}

end Record

end Formalism.L2.AtG.EntryG
end
end
end

-- Source module: Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.EntryG

section

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain MvPolynomial

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H
open Formalism.L2.AlgTh (KerStd SplitS)
open Formalism.L2.AtG.EntryG (IsEntryG Term isEntryG_zero)
open Formalism.DivisionValues (vw)

section Tower

variable {E : Type} [Field E] [NumberField E] {H M : Type} [AddCommGroup H] [Module (𝓞 E) H] [AddCommMonoid M]

def lrep (A B : Submodule (𝓞 E) H) (z : ↥A ⧸ B.comap A.subtype) : ↥A :=
  Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z

theorem latSum_eq (A B : Submodule (𝓞 E) H) (F : H → M) : latSum A B F = ∑ᶠ z, F (lrep A B z : H) := rfl

theorem mk_lrep (A B : Submodule (𝓞 E) H) (z : ↥A ⧸ B.comap A.subtype) : Submodule.Quotient.mk (lrep A B z) = z :=
  Function.surjInv_eq _ z

theorem lrep_mk_sub (A B : Submodule (𝓞 E) H) (a : ↥A) :
    ((lrep A B (Submodule.Quotient.mk a) : ↥A) : H) - (a : H) ∈ B := by
  have h := mk_lrep A B (Submodule.Quotient.mk a)
  rw [Submodule.Quotient.eq] at h
  simpa using h

theorem latSum_congr (A B : Submodule (𝓞 E) H) {F G : H → M} (h : ∀ x ∈ A, F x = G x) : latSum A B F = latSum A B G := by
  rw [latSum_eq, latSum_eq]
  exact finsum_congr fun z => h _ (lrep A B z).2

theorem latSum_tower (A B C : Submodule (𝓞 E) H) (hCB : C ≤ B) (hBA : B ≤ A) (F : H → M)
    (hF : ∀ x c, c ∈ C → F (x + c) = F x) [Finite (↥A ⧸ C.comap A.subtype)] :
    latSum A C F = latSum A B fun x => latSum B C fun y => F (x + y) := by
  classical
  let φ : (↥A ⧸ B.comap A.subtype) × (↥B ⧸ C.comap B.subtype) → (↥A ⧸ C.comap A.subtype) := fun zt =>
    Submodule.Quotient.mk ⟨(lrep A B zt.1 : H) + (lrep B C zt.2 : H), A.add_mem (lrep A B zt.1).2 (hBA (lrep B C zt.2).2)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨z, t⟩ ⟨z', t'⟩ h
    have h1 : ((lrep A B z : H) + (lrep B C t : H)) - ((lrep A B z' : H) + (lrep B C t' : H)) ∈ C := by
      have h0 := (Submodule.Quotient.eq _).1 h
      simpa using h0
    have hz : z = z' := by
      rw [← mk_lrep A B z, ← mk_lrep A B z', Submodule.Quotient.eq]
      show ((lrep A B z - lrep A B z' : ↥A) : H) ∈ B
      have e : ((lrep A B z - lrep A B z' : ↥A) : H) =
          (((lrep A B z : H) + (lrep B C t : H)) - ((lrep A B z' : H) + (lrep B C t' : H))) - (lrep B C t : H) + (lrep B C t' : H) := by
        push_cast
        abel
      rw [e]
      exact B.add_mem (B.sub_mem (hCB h1) (lrep B C t).2) (lrep B C t').2
    subst hz
    have ht : t = t' := by
      rw [← mk_lrep B C t, ← mk_lrep B C t', Submodule.Quotient.eq]
      show ((lrep B C t - lrep B C t' : ↥B) : H) ∈ C
      have e : ((lrep B C t - lrep B C t' : ↥B) : H) =
          ((lrep A B z : H) + (lrep B C t : H)) - ((lrep A B z : H) + (lrep B C t' : H)) := by
        push_cast
        abel
      rw [e]
      exact h1
    rw [ht]
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hb : (a : H) - (lrep A B (Submodule.Quotient.mk a) : H) ∈ B := by
      have := B.neg_mem (lrep_mk_sub A B a)
      simpa using this
    refine ⟨(Submodule.Quotient.mk a, Submodule.Quotient.mk ⟨_, hb⟩), ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk a
    rw [Submodule.Quotient.eq]
    have h2 := lrep_mk_sub B C ⟨_, hb⟩
    show (lrep A B (Submodule.Quotient.mk a) : H) + (lrep B C (Submodule.Quotient.mk ⟨_, hb⟩) : H) - (a : H) ∈ C
    have e : (lrep A B (Submodule.Quotient.mk a) : H) + (lrep B C (Submodule.Quotient.mk ⟨_, hb⟩) : H) - (a : H) =
        (lrep B C (Submodule.Quotient.mk ⟨_, hb⟩) : H) - ((a : H) - (lrep A B (Submodule.Quotient.mk a) : H)) := by abel
    rw [e]
    exact h2
  have hG : ∀ a : ↥A, F (lrep A C (Submodule.Quotient.mk a) : H) = F a := by
    intro a
    have h := hF (a : H) _ (lrep_mk_sub A C a)
    rwa [add_sub_cancel] at h
  have : Finite ((↥A ⧸ B.comap A.subtype) × (↥B ⧸ C.comap B.subtype)) := Finite.of_injective φ hinj
  have : Finite (↥A ⧸ B.comap A.subtype) := Finite.prod_left (↥B ⧸ C.comap B.subtype)
  have : Finite (↥B ⧸ C.comap B.subtype) := Finite.prod_right (↥A ⧸ B.comap A.subtype)
  let _ := Fintype.ofFinite (↥A ⧸ C.comap A.subtype)
  let _ := Fintype.ofFinite (↥A ⧸ B.comap A.subtype)
  let _ := Fintype.ofFinite (↥B ⧸ C.comap B.subtype)
  simp only [latSum_eq, finsum_eq_sum_of_fintype]
  rw [← (Function.Bijective.sum_comp ⟨hinj, hsurj⟩ fun w => F (lrep A C w : H)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun t _ => ?_
  exact hG _

theorem latSum_mul_left {R : Type} [NonUnitalNonAssocSemiring R] (A B : Submodule (𝓞 E) H) [Finite (↥A ⧸ B.comap A.subtype)] (r : R) (F : H → R) :
    latSum A B (fun x => r * F x) = r * latSum A B F := by
  let _ := Fintype.ofFinite (↥A ⧸ B.comap A.subtype)
  rw [latSum_eq, latSum_eq, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]

theorem mulLat_mul_le (c k : ℕ) (M : Submodule (𝓞 E) H) : mulLat (c * k) M ≤ mulLat c M := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := (mem_mulLat (c * k) M w).1 hw
  refine (mem_mulLat c M _).2 ⟨(k : 𝓞 E) • y, M.smul_mem _ hy, ?_⟩
  rw [smul_smul, Nat.cast_mul]

theorem mulLat_le_divLat (c d : ℕ) (M : Submodule (𝓞 E) H) : mulLat c M ≤ divLat d M := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := (mem_mulLat c M w).1 hw
  exact (mem_divLat d M _).2 (M.smul_mem _ (M.smul_mem _ hy))

end Tower

section Regroup

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

theorem fin_div (hN : IsSdLat N) (hN' : IsSdLat N') (cA c : ℕ) (hA : 0 < cA) (hc : 0 < c) :
    Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) :=
  kerFin S N N' hN hN' cA c hA hc

theorem fin_mul (hN : IsSdLat N) (hN' : IsSdLat N') (c c' : ℕ) (hc : 0 < c) (hc' : 0 < c') :
    Finite (↥(mulLat c (homAt S N N')) ⧸ (mulLat (c * c') (homAt S N N')).comap (mulLat c (homAt S N N')).subtype) :=
  lattice_classes_finite_refinement X a b S N N' c c' hN hN' hc hc'

end Regroup

section Cf

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

end Cf

section LatSum

variable {E : Type} [Field E] [NumberField E] {H : Type} [AddCommGroup H] [Module (𝓞 E) H]

end LatSum

section Clo

variable {X : Fields} {p : ℕ} [Fact p.Prime] {a b : ℕ} {A : Amb X} {a₀ : ℕ} {b₀ c₀' : ℤ} {ha : 0 < a₀} {hd : 0 < A.d} {lam₀ : ℂ}
  {hlam : lam₀ ≠ 0} {ι : ℂ ≃+* ℂ_[p]} {ϖ : ℂ} {pE : 𝓞 X.E} {D : ℕ} {e : ℝ}

end Clo

section Entry

variable {X : Fields} {p : ℕ} [Fact p.Prime] {a b : ℕ} (A : Amb X) (a₀ : ℕ) (b₀ c₀' : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam₀ : ℂ)
  (hlam : lam₀ ≠ 0) (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ)

end Entry

section Rec

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ}
  (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) {p : ℕ} [Fact p.Prime] (a₀ : ℕ) (b₀ c₀' : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam₀ : ℂ)
  (hlam : lam₀ ≠ 0) (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) {u : Pr.Word} (m2 : ℕ)

end Rec

section Deg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

end Deg

section Lat

variable {X : Fields} (A : Amb X) {p : ℕ} [Fact p.Prime] {a b : ℕ}

end Lat

namespace Test

end Test

end Formalism.L2.Ker
end
end
end
