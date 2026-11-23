module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDimensionInequality
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDimensionInequalitySteps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsReesAlgebraDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimensionInequality
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimensionInequalityOneGenerator

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

open Polynomial Cardinal

theorem DimensionInequalityOneGenerator.proof (h₁ : PolynomialDimensionInequality.Statement.{u})
    (h₂ : QuotientHeightAddOne.Statement.{u}) : DimensionInequalityOneGenerator.Statement.{u, v} := by
  intro A B _ _ _ _ _ _ x hx hinj P _

  let φ : A[X] →ₐ[A] B := aeval x
  have hφ : Function.Surjective φ := by
    intro b
    have hb : b ∈ (aeval x : A[X] →ₐ[A] B).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, hx]; exact Algebra.mem_top
    exact hb

  let P' : Ideal A[X] := P.comap (φ : A[X] →+* B)
  have hP' : P.under A = P'.under A := by
    ext a; simp [P', φ, Ideal.under, Ideal.mem_comap]
  have : P'.LiesOver (P.under A) := ⟨hP'⟩

  have H₁ : ofENat P'.height + Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P') ≤
      ofENat (P.under A).height + 1 := by
    have key : ∀ (q : Ideal A) [q.IsPrime] [P'.LiesOver q],
        ofENat P'.height + Algebra.trdeg (A ⧸ q) (A[X] ⧸ P') ≤ ofENat q.height + 1 := by
      intro q _ _
      obtain rfl : q = P'.under A := Ideal.LiesOver.over
      exact h₁ A P'
    exact key _

  have htr : lift.{v} (Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P')) =
      lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) := by
    let f : A[X] ⧸ P' →+* B ⧸ P := Ideal.quotientMap P (φ : A[X] →+* B) le_rfl
    have hf : Function.Bijective f :=
      ⟨Ideal.quotientMap_injective' le_rfl, Ideal.quotientMap_surjective hφ⟩
    refine AlgEquiv.lift_trdeg_eq
      (AlgEquiv.ofRingEquiv (f := (RingEquiv.ofBijective f hf : A[X] ⧸ P' ≃+* B ⧸ P)) ?_)
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp [f, φ, Ideal.Quotient.algebraMap_mk_of_liesOver]

  have H₁' : ofENat P'.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) ≤
      ofENat (P.under A).height + 1 := by
    have := Cardinal.lift_le.{v}.mpr H₁
    simpa only [lift_add, lift_ofENat, lift_one, htr] using this
  rw [← Cardinal.lift_le.{u}]
  simp only [lift_add, lift_ofENat]
  by_cases hker : RingHom.ker φ = ⊥
  ·
    have hinjφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot _).mpr hker
    let e : A[X] ≃ₐ[A] B := AlgEquiv.ofBijective φ ⟨hinjφ, hφ⟩
    have hh : P'.height = P.height := RingEquiv.height_comap (e : A[X] ≃+* B) P
    have ht : lift.{u} (Algebra.trdeg A B) = 1 := by
      rw [← e.lift_trdeg_eq, Polynomial.trdeg_of_isDomain, lift_one]
    rw [ht, ← hh]
    exact H₁'
  ·
    let e := Ideal.quotientKerAlgEquivOfSurjective hφ
    let Q : Ideal (A[X] ⧸ RingHom.ker φ) := P.comap (e : A[X] ⧸ RingHom.ker φ ≃+* B)
    have hQ : Q.comap (Ideal.Quotient.mk (RingHom.ker φ)) = P' := by
      ext f; simp [Q, P', e, Ideal.mem_comap]
    have H₂ := h₂ A[X] (RingHom.ker φ) hker Q
    rw [hQ, RingEquiv.height_comap] at H₂
    have H : ofENat P.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) + 1 ≤
        ofENat (P.under A).height + 1 :=
      calc ofENat P.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) + 1
          = ofENat (P.height + 1) + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) := by
            rw [ofENat_add, ofENat_one]; ring
        _ ≤ ofENat P'.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) :=
            add_le_add (ofENat_le_ofENat.mpr H₂) le_rfl
        _ ≤ _ := H₁'
    exact (Cardinal.add_one_le_add_one_iff.mp H).trans le_self_add

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialDimensionInequality

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

open Polynomial

theorem PolynomialDimensionInequality.proof (h : PolynomialPrimeOverZeroHeight.Statement.{u}) :
    PolynomialDimensionInequality.Statement.{u} := by
  intro A _ _ _ P _
  set p := P.under A with hp
  let I : Ideal A[X] := p.map (algebraMap A A[X])
  let Pb : Ideal (A[X] ⧸ I) := P.map (Ideal.Quotient.mk I)
  have hIP : I ≤ P := Ideal.map_comap_le
  have hPb : Pb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hIP)

  let x : A[X] ⧸ P := Ideal.Quotient.mk P X
  have key : ∀ f : A[X], aeval x (f.map (Ideal.Quotient.mk p)) = Ideal.Quotient.mk P f := by
    intro f
    rw [← Ideal.Quotient.algebraMap_eq, aeval_map_algebraMap]
    change aeval (Ideal.Quotient.mkₐ A P X) f = _
    rw [aeval_algHom_apply, aeval_X_left_apply]
    rfl
  have hsurj : Function.Surjective (aeval (R := A ⧸ p) x) := by
    intro y
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, key f⟩

  have hPb1 : Pb.height ≤ 1 := by
    let e : (A[X] ⧸ I) ≃+* (A ⧸ p)[X] := (Ideal.polynomialQuotientEquivQuotientPolynomial p).symm
    let Q : Ideal (A ⧸ p)[X] := Pb.map e
    have hQ : Q.IsPrime := Ideal.map_isPrime_of_equiv e
    have hQb : Q.comap (C : A ⧸ p →+* (A ⧸ p)[X]) = ⊥ := by
      refine le_bot_iff.mp fun a ha => ?_
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.mem_comap] at ha
      have he : C (Ideal.Quotient.mk p b) = e (Ideal.Quotient.mk I (C b)) := by
        change _ = (Ideal.polynomialQuotientEquivQuotientPolynomial p).symm
          (Ideal.Quotient.mk (p.map C) (C b))
        rw [Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, Polynomial.map_C]
      rw [he] at ha
      obtain ⟨y, hy, hye⟩ := (Ideal.mem_map_of_equiv e _).mp ha
      rw [e.injective hye, Ideal.mem_quotient_iff_mem hIP] at hy
      rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, hp, Ideal.under_def, Ideal.mem_comap,
        Polynomial.algebraMap_eq]
      exact hy
    have := h (A ⧸ p) Q hQb
    rwa [RingEquiv.height_map] at this
  have hht : P.height ≤ p.height + Pb.height := Ideal.height_le_height_add_of_liesOver p P
  by_cases hb : Pb = ⊥
  ·
    have : Nontrivial (A[X] ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top inferInstance) hIP)
    rw [hb, Ideal.height_bot, add_zero] at hht
    have htr : Algebra.trdeg (A ⧸ p) (A[X] ⧸ P) ≤ 1 :=
      (trdeg_le_of_surjective _ hsurj).trans (Polynomial.trdeg_of_isDomain).le
    exact add_le_add (Cardinal.ofENat_le_ofENat.mpr hht) htr
  ·
    obtain ⟨y, hyPb, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨f, hfP, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hyPb
    have hfI : f ∉ I := fun hf => hy0 (Ideal.Quotient.eq_zero_iff_mem.mpr hf)
    have hg : f.map (Ideal.Quotient.mk p) ≠ 0 := by
      intro hg
      apply hfI
      rw [show I = p.map C from rfl, Ideal.mem_map_C_iff]
      intro n
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, hg, coeff_zero]
    have hx : IsAlgebraic (A ⧸ p) x :=
      ⟨_, hg, by rw [key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hfP⟩
    have hadj : Algebra.adjoin (A ⧸ p) {x} = ⊤ := by
      rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
      exact hsurj
    have halg : Algebra.IsAlgebraic (A ⧸ p) (A[X] ⧸ P) := by
      have := Algebra.isAlgebraic_adjoin_singleton_iff.mpr hx
      rw [hadj] at this
      exact ⟨fun z => this z Algebra.mem_top⟩
    rw [trdeg_eq_zero_iff.mpr halg, add_zero, ← Cardinal.ofENat_one, ← Cardinal.ofENat_add,
      Cardinal.ofENat_le_ofENat]
    exact hht.trans (add_le_add le_rfl hPb1)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialPrimeOverZeroHeight

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Polynomial


attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
theorem PolynomialPrimeOverZeroHeight.proof : PolynomialPrimeOverZeroHeight.Statement := by
  intro D _ _ Q _ hQ
  let K := FractionRing D
  have disj : Disjoint ((nonZeroDivisors D).map (C : D →+* D[X]) : Set D[X]) (Q : Set D[X]) := by
    refine Set.disjoint_left.mpr fun a ⟨b, hb⟩ ha ↦ ?_
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb.1
    apply hb0
    have : b ∈ Q.comap (C : D →+* D[X]) := by
      rw [Ideal.mem_comap]
      simpa [hb.2] using ha
    rwa [hQ, Ideal.mem_bot] at this
  have hK : ringKrullDim K[X] = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one K[X] (Polynomial.not_isField K)
  have h := IsLocalization.height_map_of_disjoint ((nonZeroDivisors D).map (C : D →+* D[X]))
    (S := K[X]) Q disj
  have hP : (Q.map (algebraMap D[X] K[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors D).map (C : D →+* D[X])) K[X] Q
      ‹_› disj
  have hle : ((Q.map (algebraMap D[X] K[X])).height : WithBot ℕ∞) ≤ 1 :=
    hK ▸ Ideal.height_le_ringKrullDim_of_isPrime
  rw [h] at hle
  exact_mod_cast hle

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PQuotientHeightAddOne

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

theorem QuotientHeightAddOne.proof : QuotientHeightAddOne.Statement := by
  intro R _ _ I hI P _
  let φ : PrimeSpectrum (R ⧸ I) → PrimeSpectrum R := PrimeSpectrum.comap (Ideal.Quotient.mk I)
  have hφ : StrictMono φ := RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
  let z : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩

  have hz : ∀ q : PrimeSpectrum (R ⧸ I), z < φ q := by
    intro q
    refine lt_of_le_of_ne (show z.asIdeal ≤ (φ q).asIdeal from bot_le) fun h => hI ?_
    have hle : I ≤ (φ q).asIdeal := by
      intro x hx
      change Ideal.Quotient.mk I x ∈ q.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact q.asIdeal.zero_mem
    rw [← h] at hle
    exact le_bot_iff.mp hle
  let p : PrimeSpectrum (R ⧸ I) := ⟨P, ‹_›⟩
  have h1 : P.height = Order.height p := PrimeSpectrum.height_eq_orderHeight p
  have h2 : (P.comap (Ideal.Quotient.mk I)).height = Order.height (φ p) :=
    PrimeSpectrum.height_eq_orderHeight (φ p)
  have hne : Nonempty { l : LTSeries (PrimeSpectrum (R ⧸ I)) // l.last = p } :=
    ⟨⟨RelSeries.singleton _ p, rfl⟩⟩
  rw [h1, h2, Order.height_eq_iSup_last_eq p, iSup_subtype', ENat.iSup_add, iSup_le_iff]
  rintro ⟨l, hl⟩
  let l' : LTSeries (PrimeSpectrum R) :=
    (l.map φ hφ).cons z (by simpa using hz l.head)
  have hlast : l'.last = φ p := by simp [l', hl]
  have := Order.length_le_height (p := l') hlast.le
  simpa [l'] using this

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PReesAlgebraDim

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Polynomial

universe u

theorem ReesAlgebraDim.proof (h₁ : DimensionInequality.Statement.{u, u}) :
    ReesAlgebraDim.Statement.{u} := by
  intro A _ _ _ I hI n hn
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hinj : Function.Injective (algebraMap A (reesAlgebra I)) := by
    intro x y h
    have := congrArg (fun r : reesAlgebra I => (r : A[X])) h
    simpa using this
  apply le_antisymm
  · rw [ringKrullDim_le_iff_height_le]
    intro P hP
    have key := h₁ A (reesAlgebra I) hinj P
    have htd : Algebra.trdeg A (reesAlgebra I) ≤ 1 := by
      calc Algebra.trdeg A (reesAlgebra I) ≤ Algebra.trdeg A A[X] :=
            trdeg_le_of_injective (reesAlgebra I).val Subtype.val_injective
        _ = 1 := Polynomial.trdeg_of_isDomain
    have hp : (P.under A).height ≤ n := by
      have := Ideal.height_le_ringKrullDim_of_ne_top (inferInstance : (P.under A).IsPrime).ne_top
      rw [hn] at this
      exact_mod_cast this
    have hc : Cardinal.ofENat P.height ≤ Cardinal.ofENat ((n + 1 : ℕ) : ℕ∞) := by
      calc Cardinal.ofENat P.height
          ≤ Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (reesAlgebra I ⧸ P) :=
            le_self_add
        _ ≤ Cardinal.ofENat (P.under A).height + Algebra.trdeg A (reesAlgebra I) := key
        _ ≤ Cardinal.ofENat (n : ℕ∞) + 1 := by gcongr
        _ = Cardinal.ofENat ((n + 1 : ℕ) : ℕ∞) := by simp
    have : P.height ≤ ((n + 1 : ℕ) : ℕ∞) := Cardinal.ofENat_le_ofENat.mp hc
    exact_mod_cast this
  · let f : reesAlgebra I →+* A := (Polynomial.constantCoeff).comp (reesAlgebra I).val.toRingHom
    have hf : Function.Surjective f := fun x => ⟨algebraMap A (reesAlgebra I) x, by simp [f]⟩
    let r : reesAlgebra I := ⟨monomial 1 a, reesAlgebra.monomial_mem.mpr (by simpa using haI)⟩
    have hr0 : r ≠ 0 := by
      intro h
      have := congrArg (fun s : reesAlgebra I => (s : A[X])) h
      simp [r] at this
      exact ha0 this
    have h := ringKrullDim_succ_le_of_surjective f hf (mem_nonZeroDivisors_of_ne_zero hr0)
      (by simp [f, r])
    rw [hn] at h
    exact_mod_cast h
end NumbersDVR
end Heights
end Heights₂
end GroundTheory
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyDimensionInequality

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

theorem PolynomialDimensionInequality.full : PolynomialDimensionInequality.Statement.{u} :=
  PolynomialDimensionInequality.proof PolynomialPrimeOverZeroHeight.proof.{u}

theorem DimensionInequalityOneGenerator.full : DimensionInequalityOneGenerator.Statement.{u, v} :=
  DimensionInequalityOneGenerator.proof PolynomialDimensionInequality.full.{u}
    QuotientHeightAddOne.proof.{u}

theorem DimensionInequality.full : DimensionInequality.Statement.{u, v} :=
  DimensionInequality.proof DimensionInequalityOneGenerator.full.{u, v}
    DimensionInequalityOneGenerator.full.{v, v}

theorem ReesAlgebraDim.full : ReesAlgebraDim.Statement.{u} :=
  ReesAlgebraDim.proof DimensionInequality.full.{u, u}

theorem BlowUpModel.full : BlowUpModel.Statement.{u} :=
  BlowUpModel.proof ReesAlgebraDim.full.{u}

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end
