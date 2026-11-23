module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelRootIndependentStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelValueIndependentStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommuteStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinCkOnFlagPair
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinDivDiffExpansion
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPolyPairNum
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitFurther
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPairNum
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinRootPolyNum

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace RootPolynomialNumber

variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_rename_mul {N q : ℕ} (x : Fin N → K → ℤ) (L : Fin q → K → ℤ)
    (G : MvPolynomial (Fin N) ℤ) (Q : MvPolynomial (Fin q) ℤ) (W : Ideal (MRing ι O)) :
    classNum (Sum.elim x L) (rename Sum.inl G * rename Sum.inr Q) [] W =
      ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
  classical
  have hQ : rename Sum.inl G * rename Sum.inr Q =
      ∑ μ ∈ Q.support, Q.coeff μ •
        (rename Sum.inl G * monomial (Finsupp.mapDomain Sum.inr μ) (1 : ℤ)) := by
    conv_lhs => rw [Q.as_sum]

    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [rename_monomial, ← C_mul', ← mul_one (Q.coeff μ), ← C_mul_monomial, mul_one]
    ring
  change classNumAddHom (Sum.elim x L) [] W _ = _

  rw [hQ, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_zsmul, smul_eq_mul]
  congr 1
  change classNum (Sum.elim x L) _ [] W = _
  rw [plainPairNumber.classNum_mul_monomial, plainPairNumber.classNum_rename _ Sum.inl_injective,
    classList_mapDomain, List.append_nil, Sum.elim_comp_inl, Sum.elim_comp_inr]

end RootPolynomialNumber

theorem RootPolynomialNumber.proof : RootPolynomialNumber.Statement := by
  intro O _ _ _ K _ _ ι _ P d N x c G hG hc q L Q hQ a
  classical
  have hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q).IsHomogeneous d := by
    have h := (hG.rename_isHomogeneous (f := Fin.castAdd q)).mul
      (hQ.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show c + (d - c) = d by omega] at h
  have hcls : Sum.elim x L ∘ (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) =
      Fin.append x L := by
    funext i
    induction i using Fin.addCases <;> simp
  have hren : rename (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q)
      (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
        rename Sum.inl G * rename Sum.inr Q := by
    have e1 : (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) ∘ Fin.castAdd q = Sum.inl := by
      funext i
      simp
    have e2 : (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) ∘ Fin.natAdd N = Sum.inr := by
      funext i
      simp
    rw [map_mul, rename_rename, rename_rename, e1, e2]
  have hZ : ⇑(Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
      (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C a))) = divCycle P (C a) := by
    funext W
    simp [FlagTypings.divCycle_eq]
  have hW : ∀ W : Ideal (MRing ι O),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
                                (specialIdeal W) d (Fin.append x L) (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
        ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
    intro W
    rw [BundleExamples.polyNum_eq_classNum (Fin.append x L) finSumFinEquiv.symm (Sum.elim x L) hcls hH W,
      hren, RootPolynomialNumber.classNum_rename_mul]
  rw [BundleExamples.vEval_eq, hZ]
  simp only [hW]
  have hfin : (Function.support (divCycle P (C a))).Finite := by
    rw [← hZ, Finsupp.fun_support_eq]
    exact Finset.finite_toSet _
  rw [cycEval_eq_sum hfin]
  simp only [cycEval_eq_sum hfin, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
  ring

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagDifference

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem ck_rootNum_eq_pairNum_on_flagPair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d → fnField O (joinCoord x z) = fnField O x → ∀ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB → IsPull O x z E' E'B → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K ⊕ K' → ℤ) (f g : Fin N → MRing (Sum.elim ι ι') O), IsFlagPair ϖ (joinCoord x z) EB E'B w w' b b' f g → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ∑ μ ∈ Q.support, Q.coeff μ * pairNum (pointIdeal O (joinCoord x z)) b b' f g (psumExpansion N k) (classList (fun j => pullDeg (K' := K') (L j)) μ)) ∧ (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) → ∀ a : O, a ≠ 0 → rootNum O x d N E G L Q a = ∑ μ ∈ Q.support, Q.coeff μ * cycEval (fun W => classNum b G (classList (fun j => pullDeg (K' := K') (L j)) μ) W) (divCycle (pointIdeal O (joinCoord x z)) (C a))) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hW N V _ _ E E' hEE' K' _ _ ι' _ z hm hb EB E'B hp hp'
    w w' b b' f g hfp
  have hprime : (mcIdeal O x).IsPrime := hW.2.1.1
  obtain ⟨-, hB⟩ := (BundleExamples.isModelOver_iff O _ d).mp hm
  have hB' : IsModelOver (pointIdeal O (joinCoord x z)) d := hB
  haveI hprimeB : (pointIdeal O (joinCoord x z)).IsPrime := hm.2.1.1
  have hI := IntNumIsFieldIntersection.full (IsLocalRing.ResidueField O) (K ⊕ K') (Sum.elim ι ι')
  refine ⟨fun k hk1 hk2 q L Q hQ => ?_, fun c G hsym hG hc q L Q hQ a ha => ?_⟩
  · obtain ⟨φ, -, -, hd, hd', hf, hg⟩ :=
      ((FlagPairCharacterisation.proof O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) N V EB E'B ϖ hϖ
        hB'.multiProj).1 w w' b b' f g).mp hfp
    let F₀ : FlagModel O x d N E E' :=
      { K' := K', ι' := ι', z := z, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (FlagModel O x d N E E') := ⟨F₀⟩
    have hv : F₀.value O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
        (psum (Fin N) ℤ k) L L (fun _ => 1) (fun _ => 1) Q =
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
          (pointIdeal O (joinCoord x z)) d
          (Fin.append b fun l => pullDeg (K' := K') (L l))
          (Fin.append b' fun l => pullDeg (K' := K') (L l))
          (Fin.append f fun _ => 1) (Fin.append g fun _ => 1)
          (rename (Fin.castAdd q) (psum (Fin N) ℤ k) * rename (Fin.natAdd N) Q) := by
      show GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O _ _ d (Fin.append φ.deg _)
        (Fin.append φ.deg' _) (Fin.append φ.f fun _ => rename (liftVar ι') (1 : MRing ι O))
        (Fin.append φ.g fun _ => rename (liftVar ι') (1 : MRing ι O)) _ = _
      rw [hd, hd', hf, hg, map_one]
      rfl
    unfold ck
    rw [dite_eq_left hne]
    refine (GlobalTheory.T.flag_model_value_independent O Ω K ι x d N V E E' hW hEE'
      (Classical.choice hne) F₀ _ _ (ChernClassOnFlagPair.fieldNum_spec _ _) hI (psum (Fin N) ℤ k)
      (psum_isSymmetric _ _ k) q L L (fun _ => 1) (fun _ => 1)
      (fun l => ChernClassOnFlagPair.isVertDiv_one hprime _ (sub_self _)) k Q hk2
      (isHomogeneous_psum N k) hQ).trans ?_
    refine hv.trans ((plainPolynomialPairNumber.proof O (K ⊕ K') (Sum.elim ι ι')
      (pointIdeal O (joinCoord x z)) d N b b' f g k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) hk2 q _ Q hQ).trans ?_)
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hlen : (classList (fun j => pullDeg (K' := K') (L j)) μ).length + k = d + 1 := by
      have h := hQ (mem_support_iff.mp hμ)
      rw [ChernClassOnFlagPair.length_classList, Finsupp.degree_eq_weight_one]
      have : Finsupp.weight (fun _ => 1) μ = Finsupp.weight 1 μ := rfl
      omega
    rw [PairNumberExpansionIndependence.proof GlobalTheory.T.vertical_divisors_commute O ϖ hϖ (K ⊕ K') (Sum.elim ι ι')
      (pointIdeal O (joinCoord x z)) d hB' N b b' f g hfp.vertical k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) _ (psumExpansion N k)
      (dividedDifferenceExpansion.proof N k _ (isHomogeneous_psum N k)) (isPairExpansion_psum N k)
      _ hlen]
  · have hsame : SameGeneric O x E E := fun s _ =>
      ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
        fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
    obtain ⟨φ, -, -, hd, -, -, -⟩ :=
      ((FlagPairCharacterisation.proof O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) N V EB EB ϖ hϖ
        hB'.multiProj).1 w w b b _ _).mp (ChernClassOnFlagPair.isFlagPair_self hfp.flag)
    let F₀ : FlagModel O x d N E E :=
      { K' := K', ι' := ι', z := z, model := hm, birat := hb, EB := EB, E'B := EB,
        pull := hp, pull' := hp, flag := φ }
    have hne : Nonempty (FlagModel O x d N E E) := ⟨F₀⟩
    unfold rootNum
    rw [dite_eq_left hne]
    refine (GlobalTheory.T.flag_model_root_independent O Ω K ι x d N V E E hW hsame
      (Classical.choice hne) F₀ _ _ (ChernClassOnFlagPair.fieldNum_spec _ _) hI c G hsym hG hc q L Q hQ a
      ha).trans ?_
    have h6 := RootPolynomialNumber.proof O (K ⊕ K') (Sum.elim ι ι') (pointIdeal O (joinCoord x z)) d N b
      c G hG hc q (fun j => pullDeg (K' := K') (L j)) Q hQ a
    rw [← hd] at h6 ⊢
    exact h6

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagDifferenceStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.same_generic_flag_difference : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d → fnField O (joinCoord x z) = fnField O x → ∀ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB → IsPull O x z E' E'B → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K ⊕ K' → ℤ) (f g : Fin N → MRing (Sum.elim ι ι') O), IsFlagPair ϖ (joinCoord x z) EB E'B w w' b b' f g → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ∑ μ ∈ Q.support, Q.coeff μ * pairNum (pointIdeal O (joinCoord x z)) b b' f g (psumExpansion N k) (classList (fun j => pullDeg (K' := K') (L j)) μ)) ∧ (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) → ∀ a : O, a ≠ 0 → rootNum O x d N E G L Q a = ∑ μ ∈ Q.support, Q.coeff μ * cycEval (fun W => classNum b G (classList (fun j => pullDeg (K' := K') (L j)) μ) W) (divCycle (pointIdeal O (joinCoord x z)) (C a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_eq_pairNum_on_flagPair | exact GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_eq_pairNum_on_flagPair | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_eq_pairNum_on_flagPair <;> assumption)
end
end
