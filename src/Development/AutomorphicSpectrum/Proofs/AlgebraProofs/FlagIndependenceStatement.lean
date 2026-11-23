module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHeckeCorrespondenceOnIntegralShimuraModelStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullbackStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommute
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PAdjoinTrdegAdd
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDvrConeDimTrdeg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsTwistedDualGensExist
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsGenericProjClosureDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsGenericProjClosureDivisor
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreClosureNumber
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairBundleTrdeg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsAdjoinTrdegAdd
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairConeLinesIndep
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeLinesIndep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreClosureNumber
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureBirational
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSymmetricSpanHsymm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExpress
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorJoinPullback

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureModel

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem GenericProjClosureModel.proof (h₁ : TwistedDualGensExist.Statement)
    (h₂ : GenericProjClosureDim.Statement) (h₃ : GenericProjClosureDivisor.Statement) :
    GenericProjClosureModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB Φ _ _ _ _ e t ht
  obtain ⟨a₁, ha₁⟩ := h₁ O Ω K ι y N E B
  obtain ⟨M, φ, hφ⟩ := ha₁ a₁ le_rfl
  obtain ⟨a₁', ha₁'⟩ := h₁ O Ω K ι y N E B'
  obtain ⟨M', φ', hφ'⟩ := ha₁' a₁' le_rfl
  have hZ := h₂ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht
  obtain ⟨f₀, g₀, hD, hfg⟩ :=
    h₃ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht hZ
  exact ⟨M, M', a₁, a₁', φ, φ', hφ, hφ', hZ, f₀, g₀, hD, hfg⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHsymmPairFlagIndependence

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem HsymmPairFlagIndependence.proof (hExp : PairNumberExpansionIndependence.Statement)
    (hClos : GenericProjClosureModel.Statement) (hSeg : SegreClosureNumber.Statement) :
    HsymmPairFlagIndependence.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' v v' x x' u u' f g f₂ g₂
    hF1 hF2 n z z' fz gz hz a r R hR As Bs hAs hBs Q hQ
  classical
  have hA : (hsymmTimes N n a R).IsHomogeneous (a + r) :=
    (isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR.rename_isHomogeneous
  rcases Nat.eq_zero_or_pos N with rfl | hN
  ·
    obtain rfl : x = u := funext fun i => i.elim0
    obtain rfl : x' = u' := funext fun i => i.elim0
    obtain rfl : f = f₂ := funext fun i => i.elim0
    obtain rfl : g = g₂ := funext fun i => i.elim0
    refine hExp O ϖ hϖ K ι (pointIdeal O y) d hV (0 + n) _ _ _ _ (fun i => ?_) (a + r) _ hA As Bs
      hAs hBs Q hQ
    refine Fin.addCases (fun i => i.elim0) (fun j => ?_) i
    simp only [Fin.append_right]
    exact hz j
  ·
    let Φ := FractionRing (MvPolynomial (Fin N) Ω)
    let t : Fin N → Φ := fun i => algebraMap (MvPolynomial (Fin N) Ω) Φ (X i)
    have ht : AlgebraicIndependent Ω t :=
      (MvPolynomial.algebraicIndependent_X (Fin N) Ω).map'
        (f := IsScalarTower.toAlgHom Ω (MvPolynomial (Fin N) Ω) Φ)
        (IsFractionRing.injective (MvPolynomial (Fin N) Ω) Φ)
    obtain ⟨M, M', a₀, a₀', φ, φ', hφ, hφ', hZ, f₀, g₀, hD₀, hD₀gen⟩ :=
      hClos O ϖ hϖ Ω K ι y d hV N hN E B B' hBB' Φ w t ht
    have hC : (zetaPowTimes n (N - 1 + a) R).IsHomogeneous (N - 1 + a + r) := by
      have h := ((isHomogeneous_X ℤ (Fin.castAdd n (0 : Fin 1))).pow (N - 1 + a)).mul
        (hR.rename_isHomogeneous (f := (Fin.natAdd 1 : Fin n → Fin (1 + n))))
      rwa [one_mul] at h
    obtain ⟨Cs, hCs⟩ := exists_isPairExpansion hC
    rw [hSeg O ϖ hϖ Ω K ι y d hV N hN E B B' hBB' w w' x x' f g hF1 M M' a₀ a₀' φ φ' hφ hφ' Φ w t ht
        hZ f₀ g₀ hD₀ hD₀gen n z z' fz gz hz a r R hR As hAs Cs hCs Q hQ,
      hSeg O ϖ hϖ Ω K ι y d hV N hN E B B' hBB' v v' u u' f₂ g₂ hF2 M M' a₀ a₀' φ φ' hφ hφ' Φ w t ht
        hZ f₀ g₀ hD₀ hD₀gen n z z' fz gz hz a r R hR Bs hBs Cs hCs Q hQ]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairBundleTrdeg

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem PairBundleTrdeg.proof (hadd : AdjoinTrdegAdd.Statement) (hind : PairConeLinesIndep.Statement)
    (halg : PairConeAlg.Statement) : PairBundleTrdeg.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht
  obtain ⟨l, m', hl, hm', hal⟩ :=
    halg O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht

  let gV : (Σ k, ι k) → MvPolynomial (Option (Option K)) Φ :=
    fun q => C (algebraMap Ω Φ (y q)) * X (some (some q.1))
  let gZ : (Σ o, bundleIdx (bundleIdx ι M) M' o) → MvPolynomial (Option (Option K)) Φ :=
    fun p => C (pairProjCoord y e φ φ' t p) * X p.1
  let x : Fin N ⊕ Unit → MvPolynomial (Option (Option K)) Φ :=
    Sum.elim (fun i : Fin N => C (pairProjCoord y e φ φ' t ⟨some none, l i⟩) * X (some none))
      (fun _ : Unit => C (pairProjCoord y e φ φ' t ⟨none, m'⟩) * X none)

  have hOΩ : Function.Injective (algebraMap O Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hmem
    simpa using hmem
  have hOL : Function.Injective (algebraMap O (MvPolynomial (Option (Option K)) Φ)) := by
    rw [IsScalarTower.algebraMap_eq O Φ (MvPolynomial (Option (Option K)) Φ), IsScalarTower.algebraMap_eq O Ω Φ,
      MvPolynomial.algebraMap_eq]
    exact (C_injective _ _).comp ((algebraMap Ω Φ).injective.comp hOΩ)

  have hZ : Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O (pairProjCoord y e φ φ' t)) =
      Algebra.trdeg O (Algebra.adjoin O (Set.range gZ)) := by
    have e1 := (Ideal.quotientKerEquivRange (pointConeMap O (pairProjCoord y e φ φ' t))).trdeg_eq
    have e2 : (pointConeMap O (pairProjCoord y e φ φ' t)).range = Algebra.adjoin O (Set.range gZ) :=
      aeval_range _
    rw [e2] at e1
    exact e1

  have hw : AlgebraicIndependent Ω (fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) :=
    ((algebraicIndependent_X (Option (Option K)) Φ).restrictScalars (algebraMap Ω Φ).injective).comp _
      ((Option.some_injective _).comp (Option.some_injective _))
  let j : MvPolynomial K Ω →ₐ[O] MvPolynomial (Option (Option K)) Φ :=
    (aeval fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)).restrictScalars O
  have hjc : j.comp (pointConeMap O y) = aeval gV := by
    apply MvPolynomial.algHom_ext
    intro q
    simp [j, gV, pointConeMap, MvPolynomial.algebraMap_apply]
  have hV' : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = Algebra.trdeg O (Algebra.adjoin O (Set.range gV)) := by
    have e1 := (Ideal.quotientKerEquivRange (pointConeMap O y)).trdeg_eq
    have e2 := ((pointConeMap O y).range.equivMapOfInjective j hw).trdeg_eq
    rw [← AlgHom.range_comp, hjc, aeval_range] at e2
    exact e1.trans e2

  have hVZ : Set.range gV ⊆ Set.range gZ := by
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨some (some q.1), q.2⟩, rfl⟩
  have hxZ : Set.range x ⊆ Set.range gZ := by
    rintro _ ⟨i | _, rfl⟩
    · exact ⟨⟨some none, l i⟩, rfl⟩
    · exact ⟨⟨none, m'⟩, rfl⟩

  have hind' := hind Ω Φ K N E e (φ ∘ l) hl t ht _ hm'
  have hle : ∀ a ∈ Algebra.adjoin O (Set.range gV),
      a ∈ Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) := by
    intro a ha
    refine Algebra.adjoin_le (S := (Algebra.adjoin Ω (Set.range fun k : K =>
      (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))).restrictScalars O) ?_ ha
    rintro _ ⟨q, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
    have hc : (C (algebraMap Ω Φ (y q)) : MvPolynomial (Option (Option K)) Φ) ∈
        Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) := by
      rw [← MvPolynomial.algebraMap_apply]
      exact Subalgebra.algebraMap_mem _ _
    exact Subalgebra.mul_mem _ hc (Algebra.subset_adjoin ⟨q.1, rfl⟩)
  let f : Algebra.adjoin O (Set.range gV) →+*
      Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) :=
    { toFun := fun a => ⟨a, hle a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra (Algebra.adjoin O (Set.range gV))
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) :=
    f.toAlgebra
  have : IsScalarTower (Algebra.adjoin O (Set.range gV))
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))
      (MvPolynomial (Option (Option K)) Φ) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxind : AlgebraicIndependent (Algebra.adjoin O (Set.range gV)) x :=
    hind'.restrictScalars (K := Algebra.adjoin Ω (Set.range fun k : K =>
      (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) fun a b h => Subtype.ext (congrArg Subtype.val h :)

  have key := hadd O (MvPolynomial (Option (Option K)) Φ) hOL (Set.range gV) (Set.range gZ) (Fin N ⊕ Unit) x hxZ
    hxind (by rintro _ ⟨p, rfl⟩; exact hal p)
  rw [Set.union_eq_right.mpr hVZ] at key
  rw [hZ, hV', key, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependence

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.CommAlg.FlagIndependence

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement := by
  have hPE := PairNumberExpansionIndependence.proof
    GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute
  have hCM : GenericProjClosureModel.Statement :=
    GenericProjClosureModel.proof TwistedDualGensExist.proof
      (GenericProjClosureDim.proof DvrConeDimTrdeg.proof
        (PairBundleTrdeg.proof AdjoinTrdegAdd.proof PairConeLinesIndep.proof PairConeAlg.proof))
      (GenericProjClosureDivisor.proof TwistedDualGensExpress.proof)
  have hFM : SegreFlagClosureModel.Statement :=
    SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)
  have hSP := SegreFlagClosurePullback.proof GlobalTheory.T.pair_number_pullback hPE hFM
    PairNumberRelabel.proof VerticalDivisorJoinPullback.proof SegreFlagClosureBirational.proof
  have hSCN := SegreClosureNumber.proof hPE hFM
    GlobalTheory.T.exists_heckeCorrespondence_on_integral_shimuraModel hSP
  exact FlagIndependence.proof hPE (HsymmPairFlagIndependence.proof hPE hCM hSCN)
    SymmetricSpanHsymm.proof

end GlobalTheory.CompanionTheory.CommAlg.FlagIndependence
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependenceStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.flag_independence : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main | exact GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main | (intros; apply GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main <;> assumption)
end
end
