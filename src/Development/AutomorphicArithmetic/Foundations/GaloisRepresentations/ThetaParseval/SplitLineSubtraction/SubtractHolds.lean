module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotentiallySemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.ClTwHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCharAbove
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCharEx
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PClConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PClSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PContLeft
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCpFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PDgFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PEigSum
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PFrobSub
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PPeelAll
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSSLeft
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSplitLine
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSumDR
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwJumps
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwLoc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PWDFacts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.AlgebraicCharacterWD
public import Development.WeilBound.CoreStatements.PublishedTheorems.HeckeLAdicCharacters.Outright
public import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.GlobalArtinReciprocity

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCharFrob

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP.Sub

theorem charFrob_holds : CharFrob := by
  intro E Ω _ _ _ _ _ l _ ι art ha χ n μ h w hw hu A hA
  have hv : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∨ n = 0 := Or.inl hw
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : μ s = 1 := (h.unr_iff ha hv hA).mpr hu s hs
    simp [rk1, h1]
  · have h1 : ((μ σ : (Qbar l)ˣ) : Qbar l) = (ι.symm ((χ.val w : ℂˣ) : ℂ))⁻¹ := h.frob_unr ha hv hu hA hσ
    simp [rk1, Matrix.charpoly, Matrix.det_fin_one, h1, Polynomial.map_sub]

end UpperTheory.Gal.TP.Sub

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCharInj

section

@[expose] public section

open NumberField Neutral.B1 GlobalTheory.HeckeGal
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charInj_holds :
    CharInj := by
  intro E Ω _ _ _ _ _ l _ ι art _ χ χ' n n' μ hχ hχ'
  have hl : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
  have hfin := Ideal.finite_factors hl
  have hquot : χ * χ'⁻¹ = 1 := by
    refine Subtype.ext (GlobalTheory.FrobDense.eq_one_of_away (χ * χ'⁻¹).1
      (χ * χ'⁻¹).2.1 (χ * χ'⁻¹).2.2 hfin.toFinset fun v hv x => ?_)
    have hl' : (l : 𝓞 E) ∉ v.asIdeal :=
      fun h => hv (hfin.mem_toFinset.mpr (Ideal.dvd_span_singleton.mpr h))
    obtain ⟨σ, hσ⟩ := toAb_surjective (E := E) (Ω := Ω) (art (localIdele E v x))
    have a := hχ.loc_away (Or.inl hl') x σ hσ.symm
    have b := hχ'.loc_away (Or.inl hl') x σ hσ.symm
    have hloc : χ.loc v x = χ'.loc v x :=
      Units.ext (ι.symm.injective (a.symm.trans b))
    change χ.loc v x * (χ'.loc v x)⁻¹ = 1
    rw [hloc, mul_inv_cancel]
  exact mul_inv_eq_one.mp hquot
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PEigTransfer

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.eigTransfer_holds :
    EigTransfer := by
  intro Γ k _ _ _ _ N N' ρ ρ' hρ hρ' hcp c ⟨v, hv0, hv⟩
  have hN : N = N' := by
    have h := congrArg Polynomial.natDegree (hcp 1)
    simpa [cp, Matrix.charpoly_natDegree_eq_dim] using h
  subst hN
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ ρ' hρ hρ' (fun g => hcp g)
  refine ⟨(P : Matrix (Fin N) (Fin N) k).mulVec v, ?_, ?_⟩
  · intro h
    apply hv0
    have := congrArg (((P⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).mulVec) h
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  · intro g
    have hg : ρ g * P = P * ρ' g := by
      rw [hP g]
      group
    have hm : (ρ g : Matrix (Fin N) (Fin N) k) * P = P * ρ' g := by
      rw [← Units.val_mul, hg, Units.val_mul]
    rw [Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hv g, Matrix.mulVec_smul]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PPeelOne

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.peelOne_holds :
    DgFacts → CpFacts → EigTransfer → EigSum → SplitLine → SSLeft → PeelOne := by
  intro hDg hCp hTr hEig hSplit hSS Γ k _ _ _ _ m m' t t' r r' a a' hr hr' hne hcp
  set c := a (Fin.last t) with hc
  have hR1 : IsSSRep (sumRep r (dg a')) := GlobalTheory.BCGal.ss_sumRep _ _ hr (hDg Γ k t' a').1
  have hR2 : IsSSRep (sumRep r' (dg a)) := GlobalTheory.BCGal.ss_sumRep _ _ hr' (hDg Γ k (t + 1) a).1
  have hcpR : ∀ g, cp (sumRep r (dg a')) g = cp (sumRep r' (dg a)) g := by
    intro g
    rw [(hCp Γ k (m + 1) t').1, (hCp Γ k m' (t + 1)).1, (hDg Γ k t' a').2, (hDg Γ k (t + 1) a).2]
    exact hcp g
  have hv2 := (hEig Γ k m' (t + 1) r' a c).1 ⟨Fin.last t, rfl⟩
  have hv1 := hTr Γ k _ _ (sumRep r (dg a')) (sumRep r' (dg a)) hR1 hR2 hcpR c hv2
  have hv := (hEig Γ k (m + 1) t' r a' c).2 (fun j h => hne (Fin.last t) j h.symm) hv1
  obtain ⟨s, hs⟩ := hSplit Γ k m r hr c hv
  have hsum : IsSSRep (sumRep s (rk1 c)) := (hSS Γ k (m + 1) 0).2.1 r _ hs hr
  refine ⟨s, (hSS Γ k m 1).1 s (rk1 c) hsum, hs, ?_⟩
  intro g
  have h1 : cp r g = cp s g * (X - C ((c g : kˣ) : k)) := by
    rw [← (hCp Γ k (m + 1) 0).2.2 r _ hs g, (hCp Γ k m 1).1, (hCp Γ k m 1).2.1]
  have h2 : lin a g = lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k)) := by
    simp only [lin]
    rw [Fin.prod_univ_castSucc]
  have hX : (X - C ((c g : kˣ) : k) : k[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have key := hcp g
  rw [h1, h2] at key
  apply mul_right_cancel₀ hX
  calc cp s g * lin a' g * (X - C ((c g : kˣ) : k))
      = cp s g * (X - C ((c g : kˣ) : k)) * lin a' g := by ring
    _ = cp r' g * (lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k))) := key
    _ = cp r' g * lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k)) := by ring
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PPstOfDR

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.pstOfDR_holds :
    GlobalTheory.Published.DeRhamPotSemistable → PstOfDR := by
  intro hB l _ P AI hT E Ω _ _ _ _ _ A O _ _ _ Bw a r hr hd
  obtain ⟨T⟩ := hT
  exact hB.isPstAt T Bw r (Units.continuous_val.comp hr) hd
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractHolds

section

@[expose] public section

namespace UpperTheory.Gal.TP.Sub

theorem pstOfDR : PstOfDR := pstOfDR_holds GlobalTheory.deRham_potentiallySemistable

theorem frobSub : FrobSub := frobSub_holds cpFacts_holds

theorem clConj : ClConj := clConj_holds cpFacts_holds contLeft_holds pstOfDR

theorem clSub : ClSub := clSub_holds frobSub sumDR_holds pstOfDR wDFacts_holds

theorem clTw : ClTw := clTw_holds frobSub twLoc_holds twJumps_holds pstOfDR wDFacts_holds contLeft_holds

theorem peelAll : PeelAll :=
  peelAll_holds (peelOne_holds dgFacts_holds cpFacts_holds eigTransfer_holds eigSum_holds splitLine_holds sSLeft_holds)
    contLeft_holds clConj clSub

theorem charEx : CharEx :=
  charEx_holds PositivityTheory.Stage1.PM.heckeLAdicCharacter charFrob_holds
    (charAbove_holds PositivityTheory.Stage1.PM.heckeLAdicCharacter HodgeLocalDeRhamField.HLdR.field_outright
      (UpperTheory.Lit.CharWD.algebraicCharacterWD GlobalTheory.globalArtinReciprocity_holds HodgeLocalDeRhamField.HLdR.field_outright GlobalTheory.deRham_potentiallySemistable) pstOfDR
      contLeft_holds) charInj_holds

end UpperTheory.Gal.TP.Sub
end
end
