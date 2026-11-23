module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSubAlt
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullbackStatement
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordCompMidSwapVars
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFibreVar
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PComponentDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFibreVarieties
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimGe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinBirationalJoin
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerTail
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisTail
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreTer
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
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairJoinRight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDiv
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDivLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDivRight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreBis
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreAlt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsVerticalComponentFibre
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointNumbers
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.TypeStar
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalComponentFibre

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelJoinRight

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord pullDeg liftVar midDeg midVar FlagModel)

namespace FlagModelJoinRightAlt

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem midDeg_pullDeg (a : K → ℤ) :
    midDeg (K₂ := K₂) (pullDeg (K' := K') a) = pullDeg (K' := K₂ ⊕ K') a := by
  funext k
  rcases k with k | k | k <;> rfl

theorem midVar_comp_liftVar :
    midVar (ι := ι) (ι' := ι') ι₂ ∘ liftVar ι' = liftVar (Sum.elim ι₂ ι') :=
  rfl

theorem pullDeg_sub (a b : K → ℤ) :
    pullDeg (K' := K') a - pullDeg (K' := K') b = pullDeg (K' := K') (a - b) := by
  funext k
  cases k <;> simp [pullDeg]

end FlagModelJoinRightAlt


open FlagModelJoinRightAlt in
theorem FlagModelJoinRightAlt.proof (hVert : JoinVerticalDivisor.Statement)
    (hFlag : FlagPairJoinRight.Statement) (hNum : PairNumberJoinRight.Statement) :
    FlagModelJoinRightAlt.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' _ _ F K₂ _ ι₂ _ w hZ hfn EB E'B hp hp'
  obtain ⟨ψ, -, -, -, hdeg, hdeg', hf, hg⟩ :=
    hFlag O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w N V E E' F.EB F.E'B F.pull F.pull' F.flag EB E'B hp hp'
  refine ⟨ψ, fun I I₁ hI hI₁ G r y y' f g hv c Q hc hG hQ => ?_⟩
  have hvert : ∀ i, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (joinCoord x F.z))
      (Fin.append F.flag.deg (fun l => pullDeg (K' := F.K') (y l)) i -
        Fin.append F.flag.deg' (fun l => pullDeg (K' := F.K') (y' l)) i)
      (Fin.append F.flag.f (fun l => rename (liftVar F.ι') (f l)) i)
      (Fin.append F.flag.g (fun l => rename (liftVar F.ι') (g l)) i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact F.flag.vert j
    · simp only [Fin.append_right, pullDeg_sub]
      exact hVert O Ω K ι x F.K' F.ι' F.z _ _ _ (hv j)
  have hH : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (d + 1) := by
    have h : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (c + (d + 1 - c)) :=
      hG.rename_isHomogeneous.mul hQ.rename_isHomogeneous
    rwa [show c + (d + 1 - c) = d + 1 by omega] at h
  unfold FlagModel.value
  rw [hNum O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w d F.model hZ (hfn.trans F.birat.symm) I I₁ hI hI₁ (N + r)
    _ _ _ _ hvert _ hH]
  congr 1 <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [hdeg, hdeg', hf, hg, midDeg_pullDeg, midVar_comp_liftVar]

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinRight

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord midDeg midVar assocDeg assocVar midSwapBlocks midSwapVars
  midSwapVars_fst joinCoord_comp_midSwapVars)

namespace PairNumberJoinRight

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem assocDeg_comp_midSwapBlocks (a : K ⊕ K' → ℤ) :
    assocDeg (K₂ := K₂) a ∘ midSwapBlocks = midDeg (K₂ := K₂) a := by
  funext k
  rcases k with k | k | k <;> rfl

theorem midSwapVars_comp_midVar :
    ⇑(midSwapVars ι ι' ι₂) ∘ midVar (ι := ι) (ι' := ι') ι₂ = assocVar ι₂ := by
  funext p
  obtain ⟨k | k, i⟩ := p <;> rfl

theorem midDeg_sub (a b : K ⊕ K' → ℤ) :
    midDeg (K₂ := K₂) a - midDeg (K₂ := K₂) b = midDeg (K₂ := K₂) (a - b) := by
  funext k
  rcases k with k | k | k <;> simp [midDeg]

end PairNumberJoinRight


open PairNumberJoinRight in
theorem PairNumberJoinRight.proof (hLeft : PairNumberJoinLeft.Statement)
    (hVert : JoinVerticalDivisorRight.Statement) (hRel : PairNumberRelabelAlt.Statement) :
    PairNumberJoinRight.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w d hF hZ hfn I I₁ hI hI₁ n a a' f g hv H hH
  classical
  have hy := joinCoord_comp_midSwapVars x z w
  obtain ⟨hZL, hfnL, -, hnum⟩ := hRel O Ω (K ⊕ (K₂ ⊕ K')) (Sum.elim ι (Sum.elim ι₂ ι'))
    (K ⊕ (K' ⊕ K₂)) (Sum.elim ι (Sum.elim ι' ι₂)) midSwapBlocks (midSwapVars ι ι' ι₂) midSwapVars_fst
    (joinCoord x (joinCoord z w)) d (by rw [hy]; exact hZ)
  have hIL : IsFieldIntersection (F := IsLocalRing.ResidueField O) (ι := Sum.elim ι (Sum.elim ι' ι₂))
      (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) :=
    IntNumIsFieldIntersection.full _ _ _
  rw [hLeft O Ω K ι x K' ι' z K₂ ι₂ w d hF hZL (hfnL.trans (by rw [hy]; exact hfn)) _ I₁ hIL hI₁ n a a'
    f g hv H hH]
  have key := hnum I _ hI hIL n (fun i => assocDeg (K₂ := K₂) (a i)) (fun i => assocDeg (K₂ := K₂) (a' i))
    (fun i => rename (midVar ι₂) (f i)) (fun i => rename (midVar ι₂) (g i)) (fun i => by
      rw [hy, assocDeg_comp_midSwapBlocks, assocDeg_comp_midSwapBlocks, midDeg_sub]
      exact hVert O Ω K ι x K' ι' z K₂ ι₂ w _ _ _ (hv i)) H hH
  simp only [hy, assocDeg_comp_midSwapBlocks, rename_rename, midSwapVars_comp_midVar] at key
  exact key.symm

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumRelabel

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

namespace PairNumberRelabelAlt

theorem mcIdeal_map_rename {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
    [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] (O : Type) [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω) :
    (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (y ∘ σ)).map (rename σ) = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y :=
  pointIdeal_map_rename e σ hσ y

theorem mem_ratios {Ω₁ : Type*} [Field Ω₁] {K₀ : Type} {κ : K₀ → Type} (y : (Σ k, κ k) → Ω₁) (z : Ω₁) :
    z ∈ Set.range (fun q : (Σ k, κ k × κ k) => y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) ↔
      ∃ a b : Σ k, κ k, a.1 = b.1 ∧ y a / y b = z := by
  constructor
  · rintro ⟨⟨k, i, j⟩, rfl⟩
    exact ⟨⟨k, i⟩, ⟨k, j⟩, rfl, rfl⟩
  · rintro ⟨⟨k, i⟩, ⟨k', j⟩, h, rfl⟩
    dsimp only at h
    subst h
    exact ⟨⟨k, i, j⟩, rfl⟩

theorem fnField_comp {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} (O : Type) [CommRing O] {Ω : Type}
    [Field Ω] [Algebra O Ω] (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (y : (Σ k, ι₂ k) → Ω) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O y = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O (y ∘ σ) := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField
  congr 1
  ext z
  simp only [Set.mem_union]
  refine or_congr_right ?_
  rw [mem_ratios, mem_ratios]
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨σ.symm a, σ.symm b, ?_, by simp only [Function.comp_apply, Equiv.apply_symm_apply]⟩
    apply e.injective
    rw [← hσ, ← hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hab]
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨σ a, σ b, by rw [hσ, hσ, hab], rfl⟩

theorem pairNum_eq_intNum (hF : VerticalComponentFibre.Statement)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (I : IFamily (IsLocalRing.ResidueField O) ι) (hI : IsFieldIntersection I)
    (P : Ideal (MRing ι O)) (d : ℕ) (hP : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d)
    {r : ℕ} (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O)
    (hv : ∀ l, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P (y l - y' l) (f l) (g l))
    (G : MvPolynomial (Fin r) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I P d y y' f g G =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) P d
        y y' f g G := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hM := ((BundleExamples.isModelOver_iff O P d).1 hP).2
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
  refine Finset.sum_congr rfl fun l _ => ?_
  have hdiv := (VerticalDivisorCharacterisation.proof O K ι P ϖ (y l - y' l) (f l) (g l) hϖ hM.multiProj).1 (hv l)
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  have hW0 := Finsupp.mem_support_iff.mp hW
  have hvert : (C ϖ : MRing ι O) ∈ W := hdiv.vertical W (by rwa [← BundleExamples.ratCyc_eq])
  obtain ⟨bf, bg, hf, hg, -⟩ := hdiv.degrees
  have hvar : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d := by
    have hor : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (f l) W ≠ 0 ∨ ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (g l) W ≠ 0 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      apply hW0
      simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, hc.1, hc.2]
    rcases hor with h | h
    · have hs := JoinPointNumbers.mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι P d hM (f l) bf hf hdiv.num_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
    · have hs := JoinPointNumbers.mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι P d hM (g l) bg hg hdiv.den_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
  congr 1
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  split_ifs with h
  · exact Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI _ d _ hvar
  · rfl

end PairNumberRelabelAlt


open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal) in
theorem PairNumberRelabelAlt.proof (hF : VerticalComponentFibre.Statement) : PairNumberRelabelAlt.Statement := by
  classical
  intro O _ _ _ Ω _ _ K₁ _ ι₁ _ K₂ _ ι₂ _ e σ hσ y d hM
  have hmap := PairNumberRelabelAlt.mcIdeal_map_rename O e σ hσ y
  have hM₁ := (BundleExamples.isModelOver_iff O (mcIdeal O (y ∘ σ)) d).1 hM
  have hM₂' : IsModelOver ((mcIdeal O (y ∘ σ)).map (rename σ)) d := by
    rw [PairNumberRelabel.map_rename_eq σ]
    exact PairNumberRelabel.isModelOver_map e σ hσ _ d hM₁.2
  have hM₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d := by
    rw [← hmap]
    exact (BundleExamples.isModelOver_iff O _ d).2 ⟨⟨e hM₁.1.some⟩, hM₂'⟩
  have hvd : ∀ (b : K₂ → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι₁),
      IsVertDiv O (mcIdeal O (y ∘ σ)) (b ∘ e) f g → IsVertDiv O (mcIdeal O y) b (rename σ f) (rename σ g) := by
    intro b f g h
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have h1 := (VerticalDivisorCharacterisation.proof O K₁ ι₁ _ ϖ (b ∘ e) f g hϖ hM₁.2.multiProj).1 h
    have h2 := PairNumberRelabel.isVerticalDivisor_map e σ hσ _ ϖ b f g h1
    rw [← PairNumberRelabel.map_rename_eq σ] at h2
    rw [← hmap]
    exact (VerticalDivisorCharacterisation.proof O K₂ ι₂ _ ϖ b _ _ hϖ hM₂'.multiProj).2 h2
  refine ⟨hM₂, PairNumberRelabelAlt.fnField_comp O e σ hσ y, hvd, ?_⟩
  intro I₁ I hI₁ hI n a a' f g hfg H hH
  have hfg' : ∀ i, IsVertDiv O (mcIdeal O y) (a i - a' i) (rename σ (f i)) (rename σ (g i)) :=
    fun i => hvd (a i - a' i) (f i) (g i) (hfg i)
  rw [PairNumberRelabelAlt.pairNum_eq_intNum hF I₁ hI₁ _ d hM (fun i => a i ∘ e) (fun i => a' i ∘ e) f g hfg H,
    PairNumberRelabelAlt.pairNum_eq_intNum hF I hI _ d hM₂ a a' _ _ hfg' H,
    BundleExamples.pairNum_eq _ d _ _ f g hH, BundleExamples.pairNum_eq _ d a a' _ _ hH, ← hmap,
    PairNumberRelabel.map_rename_eq σ, PairNumberRelabel.pairNum_map e σ hσ _ a a' f g]
  rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSJoinright

section

@[expose] public section

namespace PositivityTheory.Xgn.A_s_joinright

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem fibreVarieties : FibreVarieties.Statement.{0} :=
  FibreVarieties.proof GenericFibProps.full GenericDimBound.full GenericDimGe.proof SpecialIdealCorresp.full
    SpecialIdealMultiHomog.full SupSpanMultiHomog.full MinimalPrimeMultiHomog.full SpecialQuotDim.full
    ComponentDim.proof

theorem pairNumRelabel : PairNumberRelabelAlt.Statement :=
  PairNumberRelabelAlt.proof (VerticalComponentFibre.proof fibreVarieties)

theorem of_pullback (h : PairNumberPullback.Statement) : FlagModelJoinRightAlt.Statement :=
  FlagModelJoinRightAlt.proof JoinVerticalDivisor.proof (FlagPairJoinRight.proof JoinVerticalDivisorRight.proof)
    (PairNumberJoinRight.proof
      (PairNumberJoinLeft.proof h JoinVerticalDivisorLeft.proof BirationalJoin.proof)
      JoinVerticalDivisorRight.proof pairNumRelabel)

end PositivityTheory.Xgn.A_s_joinright
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinRight

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinRightAlt.Statement :=
  PositivityTheory.Xgn.A_s_joinright.of_pullback GlobalTheory.T.pair_number_pullback

end GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinRightStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.flag_model_join_right : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinRightAlt.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main | exact GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main <;> assumption)
end
end
