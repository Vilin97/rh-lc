module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Inhabit
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitFurther
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelRootIndependentStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelValueIndependentStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommuteStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinDivCycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinIntNum
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinPointIdeal
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinVariety
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinCkOnFlagPair
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinDivDiffExpansion
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairIff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointFlagModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointNumbers
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointVertDiv
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPolyPairNum

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinPointIdeal

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar joinCoord mcIdeal mcMap)

namespace JoinPointIdeal

noncomputable section

variable {K : Type} {ι : K → Type}

def joinIdx : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≃ Unit ⊕ (Σ k, ι k) where
  toFun
    | ⟨.inl k, i⟩ => .inr ⟨k, i⟩
    | ⟨.inr _, _⟩ => .inl ()
  invFun
    | .inr p => ⟨.inl p.1, p.2⟩
    | .inl _ => ⟨.inr (), (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨(k | ⟨⟩), i⟩
    · rfl
    · show (⟨.inr (), (0 : Fin 1)⟩ : Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) = ⟨.inr (), i⟩
      congr 1
      exact (Fin.fin_one_eq_zero i).symm
  right_inv := by
    rintro (⟨⟩ | p) <;> rfl

variable (R : Type) [CommRing R]

def srcEquiv : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R ≃+*
    MvPolynomial Unit (MvPolynomial (Σ k, ι k) R) :=
  (renameEquiv R joinIdx).toRingEquiv.trans (sumRingEquiv R Unit (Σ k, ι k))

def tgtEquiv (Ω : Type) [CommRing Ω] : MvPolynomial (K ⊕ Unit) Ω ≃+* MvPolynomial Unit (MvPolynomial K Ω) :=
  (renameEquiv Ω (Equiv.sumComm K Unit)).toRingEquiv.trans (sumRingEquiv Ω Unit K)

variable (Ω : Type) [Field Ω] [Algebra R Ω]

theorem cone_comp (y : (Σ k, ι k) → Ω) :
    ((tgtEquiv (K := K) Ω : MvPolynomial (K ⊕ Unit) Ω →+* MvPolynomial Unit (MvPolynomial K Ω))).comp
        ((mcMap R (joinCoord y (ptCoord (Ω := Ω))) :
            MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →ₐ[R] MvPolynomial (K ⊕ Unit) Ω) :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial (K ⊕ Unit) Ω) =
      (MvPolynomial.map ((pointConeMap R y : MRing ι R →ₐ[R] MvPolynomial K Ω) : MRing ι R →+* _)).comp
        (srcEquiv (ι := ι) R :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial Unit (MRing ι R)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [tgtEquiv, srcEquiv, mcMap, pointConeMap, MvPolynomial.algebraMap_eq]
  · rintro ⟨(k | ⟨⟩), i⟩
    · simp [tgtEquiv, srcEquiv, mcMap, pointConeMap, joinCoord, joinIdx]
    · simp [tgtEquiv, srcEquiv, mcMap, pointConeMap, joinCoord, joinIdx, ptCoord]

theorem rename_liftVar_eq :
    ((rename (liftVar (ι := ι) ptIdx) : MRing ι R →ₐ[R] MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) :
        MRing ι R →+* MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) =
      ((srcEquiv (ι := ι) R).symm : MvPolynomial Unit (MRing ι R) →+* _).comp
        (C : MRing ι R →+* MvPolynomial Unit (MRing ι R)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [srcEquiv]
  · intro p
    simp [srcEquiv, liftVar, joinIdx]

end

end JoinPointIdeal

theorem JoinPointIdeal.proof : JoinPointIdeal.Statement := by
  intro R _ Ω _ _ K _ ι _ y
  set φ : MRing ι R →+* MvPolynomial K Ω :=
    ((pointConeMap R y : MRing ι R →ₐ[R] MvPolynomial K Ω) : MRing ι R →+* MvPolynomial K Ω) with hφ
  have h1 : mcIdeal R (joinCoord y (ptCoord (Ω := Ω))) =
      Ideal.comap (JoinPointIdeal.srcEquiv (ι := ι) R :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial Unit (MRing ι R))
        (RingHom.ker (MvPolynomial.map (σ := Unit) φ)) := by
    ext f
    have hc := RingHom.congr_fun (JoinPointIdeal.cone_comp R Ω y) f
    simp only [RingHom.comp_apply] at hc
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hc]
    simp only [RingHom.coe_coe, EmbeddingLike.map_eq_zero_iff]
    exact RingHom.mem_ker
  rw [h1, pointIdeal, show RingHom.ker (pointConeMap R y) = RingHom.ker φ from rfl, ← Ideal.map_coe, JoinPointIdeal.rename_liftVar_eq, ← Ideal.map_map, Ideal.map_coe, Ideal.map_symm, ← MvPolynomial.ker_map]
  rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinVariety

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)

noncomputable section

namespace JoinVariety

variable {K : Type} {ι : K → Type}

def varEquiv : Option (Σ k, ι k) ≃ (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) where
  toFun
    | none => ⟨.inr (), (0 : Fin 1)⟩
    | some p => liftVar (ι := ι) ptIdx p
  invFun
    | ⟨.inl k, i⟩ => some ⟨k, i⟩
    | ⟨.inr _, _⟩ => none
  left_inv := by
    rintro (_ | ⟨k, i⟩) <;> rfl
  right_inv := by
    rintro ⟨(k | u), i⟩
    · rfl
    · cases u
      have : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst this
      rfl

theorem liftVar_injective : Function.Injective (liftVar (ι := ι) ptIdx) :=
  (varEquiv (ι := ι)).injective.comp (Option.some_injective _)

def retr (F : Type) [Field F] :
    MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) F →ₐ[F] MvPolynomial (Σ k, ι k) F :=
  aeval fun t => match t with
    | ⟨.inl k, i⟩ => X ⟨k, i⟩
    | ⟨.inr _, _⟩ => 1

theorem retr_rename (F : Type) [Field F] (p : MvPolynomial (Σ k, ι k) F) :
    retr F (rename (liftVar (ι := ι) ptIdx) p) = p := by
  have : (retr F).comp (rename (liftVar (ι := ι) ptIdx)) = AlgHom.id F _ := by
    ext ⟨k, i⟩
    simp [retr, liftVar]
  exact congrArg (fun φ => φ p) this

end JoinVariety

open JoinVariety in
theorem JoinVariety.proof : JoinVariety.Statement := by
  intro F _ K _ ι _ V n hV
  obtain ⟨⟨hprime, ⟨S0, hS0, hspan⟩, hrel⟩, hdim⟩ := hV
  set V' := V.map (rename (liftVar (ι := ι) ptIdx))

  let Φ : Polynomial (MvPolynomial (Σ k, ι k) F) ≃ₐ[F] MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) F :=
    (optionEquivLeft F (Σ k, ι k)).symm.trans (renameEquiv F varEquiv)
  have hΦC : (Φ : Polynomial (MvPolynomial (Σ k, ι k) F) →+* _).comp Polynomial.C =
      (rename (liftVar (ι := ι) ptIdx) : MvPolynomial (Σ k, ι k) F →ₐ[F] _).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 : (optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (C r)) = C r := by
        rw [AlgEquiv.symm_apply_eq]; simp
      show renameEquiv F varEquiv ((optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (C r))) = _
      rw [h1]
      simp
    · intro s
      have h1 : (optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (X s)) = X (some s) := by
        rw [AlgEquiv.symm_apply_eq]; simp
      show renameEquiv F varEquiv ((optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (X s))) = _
      rw [h1]
      simp [varEquiv]
  have hV' : V' = (V.map (Polynomial.C : MvPolynomial (Σ k, ι k) F →+* Polynomial (MvPolynomial (Σ k, ι k) F))).map (Φ : Polynomial (MvPolynomial (Σ k, ι k) F) →+* _) := by
    rw [Ideal.map_map, hΦC]
    rfl

  have hmem : ∀ y, y ∈ V' → retr F y ∈ V := by
    have : V' ≤ V.comap (retr F : _ →ₐ[F] MvPolynomial (Σ k, ι k) F).toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro v hv
      simpa [Ideal.mem_comap, retr_rename] using hv
    exact fun y hy => this hy
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hV']
    exact Ideal.map_isPrime_of_equiv _
  · refine ⟨rename (liftVar (ι := ι) ptIdx) '' S0, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨a, ha⟩ := hS0 f hf
      refine ⟨Sum.elim a 0, ?_⟩
      classical
      intro m hm k
      rw [support_rename_of_injective liftVar_injective] at hm
      obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
      cases k with
      | inl k =>
        change ∑ i : ι k, (Finsupp.mapDomain (liftVar (ι := ι) ptIdx) m0)
          (liftVar (ι := ι) ptIdx ⟨k, i⟩) = a k
        simp only [Finsupp.mapDomain_apply_of_injective liftVar_injective]
        exact ha m0 hm0 k
      | inr u =>
        simp only [Sum.elim_inr, Pi.zero_apply]
        refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
        rintro ⟨p, hp⟩
        cases hp
    · change V.map _ = _
      rw [hspan, Ideal.map_span]
  · rintro (k | u)
    · obtain ⟨i, hi⟩ := hrel k
      refine ⟨i, fun h => hi ?_⟩
      have := hmem _ h
      simpa [retr] using this
    · refine ⟨(0 : Fin 1), fun h => hprime.ne_top ?_⟩
      have := hmem _ h
      rw [Ideal.eq_top_iff_one]
      simpa [retr] using this
  · have e1 : (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (Sum.elim ι ptIdx) ⧸ V') ≃+*
        Polynomial (MvPolynomial (Σ k, ι k) F ⧸ V) :=
      (Ideal.quotientEquiv _ _ Φ.toRingEquiv hV').symm.trans
        (Ideal.polynomialQuotientEquivQuotientPolynomial V).symm
    refine (ringKrullDim_eq_of_ringEquiv
      (S := Polynomial (MvPolynomial (Σ k, ι k) F ⧸ V)) e1).trans ?_
    rw [Polynomial.ringKrullDim_of_isNoetherianRing]
    change ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ V) + 1 = _
    rw [hdim, Fintype.card_sum, Fintype.card_unit]
    norm_cast

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChernClassOnFlagPair

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial

open GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial

theorem rootPolyNum : RootPolynomialNumber.Statement := by
  intro O _ _ _ K _ _ ι _ P d N x c G hG hc q L Q hQ a
  have hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q :
      MvPolynomial (Fin (N + q)) ℤ).IsHomogeneous d := by
    have h3 := (hG.rename_isHomogeneous (f := Fin.castAdd q)).mul
      (hQ.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show c + (d - c) = d by omega] at h3
  have hZ : ⇑(Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
      (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C a))) = divCycle P (C a) := by
    funext W
    simp [FlagTypings.divCycle_eq]
  have hfin : (Function.support (divCycle P (C a))).Finite := by
    rw [← hZ]
    exact Finsupp.hasFiniteSupport _
  have hcast : Fin.append x L ∘ Fin.castAdd q = x := by
    funext i
    simp [Fin.append_left]
  have hnat : Fin.append x L ∘ Fin.natAdd N = L := by
    funext j
    simp [Fin.append_right]
  have key : ∀ W : Ideal (MRing ι O), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
      (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) (specialIdeal W) d (Fin.append x L)
      (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
      ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
    intro W
    rw [BundleExamples.polyNum_eq_classNum (Fin.append x L) (Equiv.refl _) (Fin.append x L) rfl hH W]
    simp only [Equiv.coe_refl, rename_id_apply]
    rw [plainPolynomialPairNumber.classNum_mul_tail _ L _ hnat]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [plainPairNumber.classNum_rename _ (Fin.castAdd_injective _ _), hcast]
  rw [BundleExamples.vEval_eq, hZ]
  simp only [key, cycEval_eq_sum hfin, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
  ring

theorem main : ChernClassOnFlagPair.Statement :=
  ChernClassOnFlagPair.proof
    (JoinPointFlagModel.proof FlagPairCharacterisation.proof JoinPointModel.proof
      JoinPointVerticalDivisor.proof)
    (JoinPointNumbers.proof JoinPointIdeal.proof JoinDivCycle.proof JoinVariety.proof
      JoinIntNum.proof PairNumberJoinLeft.verticalComponentFibre)
    GlobalTheory.T.flag_model_value_independent GlobalTheory.T.flag_model_root_independent plainPolynomialPairNumber.proof rootPolyNum
    (PairNumberExpansionIndependence.proof GlobalTheory.T.vertical_divisors_commute) dividedDifferenceExpansion.proof

end GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChernClassOnFlagPairStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.chern_class_on_flag_pair : GroundTheory.Heights₂.Heights.NumbersDVR.ChernClassOnFlagPair.Statement := by
  first | exact @GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial.main | exact GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial.main | (intros; apply GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial.main <;> assumption)
end
end
