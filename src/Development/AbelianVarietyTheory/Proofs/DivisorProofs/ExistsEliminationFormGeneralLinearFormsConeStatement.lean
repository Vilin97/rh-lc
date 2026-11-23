module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishTransferOfVanishOverAlgebraicClosureStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMultiplicityDvdFixFirstBlock

section

@[expose] public section

open MvPolynomial GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra

set_option autoImplicit false

namespace GlobalTheory.ChowSection

theorem totalDegree_of_isChowFormInt {k : Type} [Field k] {N e d : ℕ}
    {Q : Ideal (MvPolynomial (Fin N) k)} {g : MvPolynomial (Fin (e + 1) × Fin N) k}
    (h : IsChowFormInt Q e d g) : g.totalDegree = (e + 1) * d := by
  rw [((isMultiHomogeneous_iff_block.1 h.homog).isHomogeneous).totalDegree h.ne_zero]
  simp

end GlobalTheory.ChowSection
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalEqZeroOfPoint

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

namespace GlobalTheory.HSElim

attribute [local instance] MvPolynomial.gradedAlgebra

theorem aeval_eq_zero_of_point {F K : Type} [Field F] [Field K] [Algebra F K] [IsAlgClosure F K]
    {N e δ : ℕ} {P : Ideal (MvPolynomial (Fin N) F)} {f : MvPolynomial (Fin (e + 1) × Fin N) F}
    (hf : IsChowFormInt P e δ f) (s : Fin (e + 1) → Fin N → K) (y : Fin N → K) (hy : y ≠ 0)
    (hyP : ∀ a ∈ P, aeval y a = 0) (hs : ∀ i, ∑ j, s i j * y j = 0) :
    aeval (fun p : Fin (e + 1) × Fin N => s p.1 p.2) f = 0 := by
  let φ : K ≃ₐ[F] AlgebraicClosure F := IsAlgClosure.equiv F K (AlgebraicClosure F)
  have hmap : ∀ {σ : Type} (x : σ → K) (a : MvPolynomial σ F),
      aeval (fun i => φ (x i)) a = φ (aeval x a) := fun x a =>
    (AlgHom.congr_fun (MvPolynomial.comp_aeval (f := x) (φ : K →ₐ[F] AlgebraicClosure F)) a).symm
  have key : aeval (fun p : Fin (e + 1) × Fin N => φ (s p.1 p.2)) f = 0 := by
    refine (hf.zero_iff _).2 ⟨fun j => φ (y j), ?_, fun a ha => ?_, fun i => ?_⟩
    · intro h
      apply hy
      funext j
      have := congrFun h j
      simpa using this
    · rw [hmap, hyP a ha, map_zero]
    · have := congrArg φ (hs i)

      simpa [map_sum, map_mul] using this
  rw [hmap (fun p : Fin (e + 1) × Fin N => s p.1 p.2)] at key
  simpa using key

theorem exists_elim_form : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ)
    (I : Ideal (MvPolynomial (Fin N) F)) (g : MvPolynomial (Fin N) F), 1 ≤ D → I.IsPrime →
    (∀ a ∈ I, ∀ n : ℕ, homogeneousComponent n a ∈ I) →
    ringKrullDim (MvPolynomial (Fin N) F ⧸ I) = (D + 1 : ℕ) → g.IsHomogeneous d → g ∉ I →
    ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ Q.totalDegree ≤ D * d * hilbertDegree I ∧
      ∀ (K : Type) [Field K] [Algebra F K] [IsAlgClosure F K] (s : Fin D → Fin N → K)
        (y : Fin N → K), y ≠ 0 → (∀ a ∈ I, aeval y a = 0) → aeval y g = 0 →
        (∀ i, ∑ j, s i j * y j = 0) → aeval (fun p : Fin D × Fin N => s p.1 p.2) Q = 0 := by
  intro F _ _ D N d I g hD hp hcomp hdim hg hgI
  obtain ⟨e, rfl⟩ : ∃ e, D = e + 1 := ⟨D - 1, by omega⟩
  have hIh := GlobalTheory.ChowExists.isHomogeneous_of_component hcomp
  obtain ⟨f0, hf0⟩ := GlobalTheory.ChowExists.exists_isChowFormInt hp hIh hdim
  obtain ⟨i0, hi0⟩ := GlobalTheory.ChowExists.exists_X_notMem hf0
  have hJh := isHomogeneous_sup_span_singleton hIh hg
  have hex : ∀ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset,
      ∃ f : MvPolynomial (Fin (e + 1) × Fin N) F, IsChowFormInt P e (hilbertDegree P) f := by
    intro P hP
    rw [Set.Finite.mem_toFinset] at hP
    have hPp := hP.1.1.1
    obtain ⟨e', h1, h2⟩ := ringKrullDim_of_mem_projComponents_sup hIh hdim hg hgI hP
    obtain rfl : e = e' := by omega
    exact GlobalTheory.ChowExists.exists_isChowFormInt hPp (isHomogeneous_of_mem_projComponents hJh hP) h2
  choose! f hf using hex
  refine ⟨∏ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset, f P, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun P hP => (hf P hP).ne_zero
  · refine (totalDegree_finsetProd _ _).trans ?_
    have h1 : ∑ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset, (f P).totalDegree =
        (e + 1) * projSetDegree (I ⊔ Ideal.span {g}) := by
      rw [projSetDegree, Finset.mul_sum]
      exact Finset.sum_congr rfl fun P hP => GlobalTheory.ChowSection.totalDegree_of_isChowFormInt (hf P hP)
    rw [h1, mul_assoc]
    exact Nat.mul_le_mul_left _ (projSetDegree_sup_le_of_isPrime hIh hi0 hg hgI)
  · intro K _ _ _ s y hy hyI hyg hs
    rw [map_prod]
    let Jy : Ideal (MvPolynomial (Fin N) F) := RingHom.ker (aeval y : MvPolynomial (Fin N) F →ₐ[F] K)
    have hJy : I ⊔ Ideal.span {g} ≤ Jy := sup_le (fun a ha => (RingHom.mem_ker).2 (hyI a ha))
      ((Ideal.span_singleton_le_iff_mem _).2 ((RingHom.mem_ker).2 hyg))
    have : Jy.IsPrime := RingHom.ker_isPrime _
    obtain ⟨P, hPmin, hPle⟩ := Ideal.exists_minimalPrimes_le hJy
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
    have hPc : P ∈ projComponents (I ⊔ Ideal.span {g}) :=
      ⟨hPmin, i, fun h => hi (by simpa using (RingHom.mem_ker).1 (hPle h))⟩
    have hPf : P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset :=
      (Set.Finite.mem_toFinset _).2 hPc
    exact Finset.prod_eq_zero hPf (aeval_eq_zero_of_point (hf P hPf) s y hy
      (fun a ha => (RingHom.mem_ker).1 (hPle ha)) hs)

end GlobalTheory.HSElim
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEliminationFormGeneralLinearFormsCone

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem exists_elim_form_of_field : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F)) (g : MvPolynomial (Fin N) F), 1 ≤ D → I.IsPrime → (∀ a ∈ I, ∀ n : ℕ, homogeneousComponent n a ∈ I) → ringKrullDim (MvPolynomial (Fin N) F ⧸ I) = (D + 1 : ℕ) → g.IsHomogeneous d → g ∉ I → ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ ∀ (K : Type) [Field K] [Algebra F K] (s : Fin D → Fin N → K) (y : Fin N → K), y ≠ 0 → (∀ a ∈ I, aeval y a = 0) → aeval y g = 0 → (∀ i, ∑ j, s i j * y j = 0) → aeval (fun p : Fin D × Fin N => s p.1 p.2) Q = 0 := by
  intro F _ _ D N d I g hD hI hhom hdim hg hgI
  obtain ⟨Q, hQ0, -, hQ⟩ := GlobalTheory.HSElim.exists_elim_form F D N d I g hD hI hhom hdim hg hgI
  refine ⟨Q, hQ0, ?_⟩
  intro K _ _ s y hy hyI hyg hlin
  classical
  let ey : Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) := fun j => Sum.inr (Sum.inl j)
  let ez : Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) := fun j => Sum.inr (Sum.inr j)
  let gens : Set (MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F) :=
    ((rename ey) '' (I : Set _) ∪ {rename ey g}) ∪
    (Set.range (fun i : Fin D => ∑ j, X (Sum.inl (i, j)) * X (ey j)) ∪ {∑ j, X (ez j) * X (ey j) - 1})
  let f := rename (Sum.inl : Fin D × Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) Q
  have hclos : ∀ x : (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) → AlgebraicClosure F,
      (∀ p ∈ Ideal.span gens, aeval x p = 0) → aeval x f = 0 := by
    intro x hx
    have h' : ∀ p ∈ gens, aeval x p = 0 := fun p hp => hx p (Ideal.subset_span hp)
    have hz : ∑ j, x (ez j) * x (ey j) = 1 := by
      have := h' _ (Or.inr (Or.inr rfl))
      simpa [sub_eq_zero] using this
    have hy0 : (fun j => x (ey j)) ≠ 0 := by
      intro h0
      have : ∑ j, x (ez j) * x (ey j) = 0 := by
        simp [show ∀ j, x (ey j) = 0 from fun j => congrFun h0 j]
      rw [hz] at this
      exact one_ne_zero this
    simp only [f, aeval_rename]
    exact hQ (AlgebraicClosure F) (fun i j => x (Sum.inl (i, j))) (fun j => x (ey j)) hy0
      (fun a ha => by
        have := h' _ (Or.inl (Or.inl ⟨a, ha, rfl⟩))
        simpa [aeval_rename, Function.comp_def] using this)
      (by
        have := h' _ (Or.inl (Or.inr rfl))
        simpa [aeval_rename, Function.comp_def] using this)
      (fun i => by
        have := h' _ (Or.inr (Or.inl ⟨i, rfl⟩))
        simpa using this)
  obtain ⟨j0, hj0⟩ : ∃ j0, y j0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hy (funext hcon)
  let z : Fin N → K := fun j => if j = j0 then (y j0)⁻¹ else 0
  let x0 : (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) → K := Sum.elim (fun p => s p.1 p.2) (Sum.elim y z)
  have hx0 : ∀ p ∈ Ideal.span gens, aeval x0 p = 0 := by
    intro p hp
    have hle : Ideal.span gens ≤ RingHom.ker (aeval x0 : MvPolynomial _ F →ₐ[F] K) := by
      rw [Ideal.span_le]
      rintro q ((⟨a, ha, rfl⟩ | rfl) | (⟨i, rfl⟩ | rfl))
      · simpa [aeval_rename, Function.comp_def, x0, ey] using hyI a ha
      · simpa [aeval_rename, Function.comp_def, x0, ey] using hyg
      · simpa [x0, ey] using hlin i
      · simp [x0, ey, ez, z, hj0]
    exact hle hp
  have := GlobalTheory.T.vanish_transfer_of_vanish_over_algebraicClosure F ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) (Ideal.span gens) f hclos K x0 hx0
  simpa [f, aeval_rename, Function.comp_def, x0] using this

end GlobalTheory.HSShort
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEliminationFormGeneralLinearFormsConeStatement

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.exists_eliminationForm_generalLinearForms_cone : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F)) (g : MvPolynomial (Fin N) F), 1 ≤ D → I.IsPrime → (∀ a ∈ I, ∀ n : ℕ, homogeneousComponent n a ∈ I) → ringKrullDim (MvPolynomial (Fin N) F ⧸ I) = (D + 1 : ℕ) → g.IsHomogeneous d → g ∉ I → ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ ∀ (K : Type) [Field K] [Algebra F K] (s : Fin D → Fin N → K) (y : Fin N → K), y ≠ 0 → (∀ a ∈ I, aeval y a = 0) → aeval y g = 0 → (∀ i, ∑ j, s i j * y j = 0) → aeval (fun p : Fin D × Fin N => s p.1 p.2) Q = 0 := by
  first | exact @GlobalTheory.HSShort.exists_elim_form_of_field | exact GlobalTheory.HSShort.exists_elim_form_of_field | (intros; apply GlobalTheory.HSShort.exists_elim_form_of_field <;> assumption)
end
end
