module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailFurther
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideRest
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailExtra
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PModelGenericPoint
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailAlt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockVecSegreJoin
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideLast
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftVal
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
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.ModelSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideSide
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreInclWeightedHomogeneousComponent
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

-- Source module: GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailBis

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W →
      IsMultiProjPrime (segreLift ι F W)

theorem SegreLiftPrime.hyps : IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) :=
  NumbersDVR.isMultiProjPrime_bot

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreFibresNef

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

theorem segreFibresNef_of_map (hA : SegreLiftComap.Statement) (hB : SegreLiftPrime.Statement)
    (hC : SegreLiftRelDim.Statement) (hN : SegreLiftIntNum.Statement)
    (hD : SegreFibreIdeal.Statement) (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    (F : Type) [Field F] (φ : O →+* F) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (β : K → ℤ) :
    IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal F ((mIdealOver O (segreJoin y)).map (MvPolynomial.map φ))
                              (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) ↔
      IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal F ((mIdealOver O y).map (MvPolynomial.map φ)) β := by
  obtain ⟨hrel, hle, hlift⟩ := hD O Ω F φ K ι y
  constructor
  · intro h W hW hPW hdim
    have hpos := h (segreLift ι F W) (hB F K ι W hW) (hlift W hPW)
      (by rw [hC F K ι W hW]; exact hdim)
    rwa [hN F K ι W hW β] at hpos
  · intro h W' hW' hPW' hdim
    obtain ⟨hWp, heq⟩ := hA F K ι W' hW' fun g hg => hPW' (hrel hg)
    have hPW : (mIdealOver O y).map (MvPolynomial.map φ) ≤ W'.comap (segreIncl ι F) :=
      hle.trans (Ideal.comap_mono hPW')
    have hdimW : relDim (W'.comap (segreIncl ι F)) = ((1 : ℕ) : WithBot (WithTop ℤ)) := by
      rw [← hC F K ι _ hWp, ← heq]
      exact hdim
    have hpos := h _ hWp hPW hdimW
    rw [heq, hN F K ι _ hWp β]
    exact hpos

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftMapMap

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

noncomputable section

namespace SegreFibreIdeal

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] {ι : K → Type}

def thetaVal (ι : K → Type) (R : Type) [CommRing R] : (Σ k, segreIdx ι k) → Polynomial (MRing ι R)
  | ⟨Sum.inl _, c⟩ => Polynomial.X * Polynomial.C (∏ k, X ⟨k, c k⟩)
  | ⟨Sum.inr k, i⟩ => Polynomial.C (X ⟨k, i⟩)

def theta (ι : K → Type) (R : Type) [CommRing R] : MRing (segreIdx ι) R →+* Polynomial (MRing ι R) :=
  eval₂Hom (Polynomial.C.comp C) (thetaVal ι R)

def chi (K : Type) [Fintype K] : MvPolynomial (Unit ⊕ K) Ω →+* Polynomial (MvPolynomial K Ω) :=
  eval₂Hom (Polynomial.C.comp C)
    (Sum.elim (fun _ => Polynomial.X * Polynomial.C (∏ k, X k)) (fun k => Polynomial.C (X k)))

theorem map_cone_theta (y : (Σ k, ι k) → Ω) :
    (Polynomial.mapRingHom (mConeMapOver O y).toRingHom).comp (theta ι O) =
      (chi K).comp (mConeMapOver O (segreJoin y)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [theta, chi, mConeMapOver]
  · rintro ⟨(u | k), i⟩
    · simp [theta, thetaVal, chi, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec,
        IndefiniteRowSideFullHecke.Kleiman2.oneBlock, NumbersDVR.segreVec, Polynomial.map_prod, Finset.prod_mul_distrib]
      ring
    · simp [theta, thetaVal, chi, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec]

theorem segreLiftMap_map (F : Type) [Field F] (φ : O →+* F) (W : Ideal (MRing ι F)) :
    (segreLiftMap ι F W).toRingHom.comp (MvPolynomial.map φ) =
      (Polynomial.mapRingHom ((Ideal.Quotient.mk W).comp (MvPolynomial.map φ))).comp (theta ι O) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [theta, segreLiftMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coe_eval₂Hom, eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C, map_C, aeval_C]
    rfl
  · rintro ⟨(u | k), i⟩
    · simp [theta, thetaVal, segreLiftMap, segreLiftVal, Polynomial.map_prod]
    · simp [theta, thetaVal, segreLiftMap, segreLiftVal]

end SegreFibreIdeal

open SegreFibreIdeal in
theorem SegreFibreIdeal.proof : SegreFibreIdeal.Statement := by
  intro O _ Ω _ _ F _ φ K _ _ ι _ y
  refine ⟨?_, ?_, ?_⟩
  · rintro g ⟨c, d, rfl⟩
    have hm : (segreY c * segreMon d - segreY d * segreMon c : MRing (segreIdx ι) O) ∈
        mIdealOver O (segreJoin y) := by
      simp only [mIdealOver, RingHom.mem_ker, map_sub, map_mul, map_prod, segreY, segreMon,
        mConeMapOver, aeval_X, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec, IndefiniteRowSideFullHecke.Kleiman2.oneBlock,
        NumbersDVR.segreVec, Sum.elim_inr, Finset.prod_mul_distrib]
      ring
    have := Ideal.mem_map_of_mem (MvPolynomial.map φ) hm
    rw [SetLike.mem_coe]
    convert this using 1
    simp [segreY, segreMon, map_prod]
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    simp only [Ideal.mem_comap]
    have hr : segreIncl ι F (MvPolynomial.map φ f) = MvPolynomial.map φ (segreIncl ι O f) := by
      simp [segreIncl, MvPolynomial.map_rename]
    rw [hr]
    refine Ideal.mem_map_of_mem _ ?_
    have key : (mConeMapOver O (segreJoin y)).toRingHom.comp (segreIncl ι O).toRingHom =
        (rename (R := Ω) (Sum.inr : K → Unit ⊕ K)).toRingHom.comp (mConeMapOver O y).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [segreIncl, mConeMapOver]
      · rintro ⟨k, i⟩
        simp [segreIncl, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec]
    have hc : mConeMapOver O (segreJoin y) (segreIncl ι O f) =
        rename Sum.inr (mConeMapOver O y f) := by
      simpa using congrArg (fun g => g f) key
    rw [mIdealOver, RingHom.mem_ker] at hf ⊢
    rw [hc, hf, map_zero]
  · intro W hW
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, segreLift, RingHom.mem_ker]
    have h1 := congrArg (fun g => g f) (segreLiftMap_map F φ W)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
    rw [h1]
    have h2 := congrArg (fun g => g f) (map_cone_theta (O := O) y)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
    rw [mIdealOver, RingHom.mem_ker] at hf
    rw [hf, map_zero] at h2
    ext n
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_zero,
      RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    apply hW
    apply Ideal.mem_map_of_mem
    rw [mIdealOver, RingHom.mem_ker]
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) h2
    simpa [Polynomial.coeff_map] using this

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeSegreLift

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

noncomputable section

namespace SegreNef

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem map_id_ideal {σ : Type*} (I : Ideal (MvPolynomial σ F)) :
    I.map (MvPolynomial.map (RingHom.id F)) = I := by
  have h : (MvPolynomial.map (RingHom.id F) : MvPolynomial σ F →+* MvPolynomial σ F) = RingHom.id _ :=
    RingHom.ext MvPolynomial.map_id
  rw [h, Ideal.map_id]

theorem comap_segreLift (W : Ideal (MRing ι F)) : (segreLift ι F W).comap (segreIncl ι F) = W := by
  have h : (segreLiftMap ι F W).comp (segreIncl ι F) =
      (Polynomial.CAlgHom : (MRing ι F ⧸ W) →ₐ[F] Polynomial (MRing ι F ⧸ W)).comp
        (Ideal.Quotient.mkₐ F W) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [segreIncl, segreLiftMap, segreLiftVal]
  ext g
  rw [Ideal.mem_comap, segreLift, RingHom.mem_ker]
  have hg := congrArg (fun φ => φ g) h
  simp only [AlgHom.comp_apply] at hg
  rw [hg, Polynomial.CAlgHom_apply, Polynomial.C_eq_zero, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem]

theorem genPt_block_ne_zero (W : Ideal (MRing ι F)) [W.IsPrime] (hW : IsMultiProjPrime W) :
    ∀ k, ∃ i, ModelGenericPoint.genPt W ⟨k, i⟩ ≠ 0 := fun k => by
  obtain ⟨i, hi⟩ := hW.relevant k
  exact ⟨i, (ModelGenericPoint.genPt_ne_zero W _).mpr hi⟩

theorem segreJoin_block_ne_zero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, segreJoin y ⟨k, i⟩ ≠ 0
  | Sum.inl () => ⟨fun k => (hy k).choose,
      show ∏ k, y ⟨k, (hy k).choose⟩ ≠ 0 from Finset.prod_ne_zero_iff.mpr fun k _ => (hy k).choose_spec⟩
  | Sum.inr k => hy k

theorem segreLift_eq_mIdealOver (W : Ideal (MRing ι F)) [W.IsPrime] (hW : IsMultiProjPrime W) :
    segreLift ι F W = mIdealOver F (segreJoin (ModelGenericPoint.genPt W)) := by
  have hy : mIdealOver F (ModelGenericPoint.genPt W) = W :=
    ModelGenericPoint.mIdealOver_genPt W hW.multiHomog
  have hP' : IsMultiProjPrime (mIdealOver F (segreJoin (ModelGenericPoint.genPt W))) :=
    isMultiProjPrime_mIdealOver _ (segreJoin_block_ne_zero _ (genPt_block_ne_zero W hW))
  obtain ⟨hrel, hle, hlift⟩ := SegreFibreIdeal.proof F _ F (RingHom.id F) K ι (ModelGenericPoint.genPt W)
  simp only [map_id_ideal] at hrel hle hlift
  have hc : (mIdealOver F (segreJoin (ModelGenericPoint.genPt W))).comap (segreIncl ι F) = W := by
    refine le_antisymm ?_ (hy.ge.trans hle)
    have h := hlift W hy.le
    exact (Ideal.comap_mono h).trans (comap_segreLift W).le
  calc segreLift ι F W
      = segreLift ι F ((mIdealOver F (segreJoin (ModelGenericPoint.genPt W))).comap (segreIncl ι F)) := by
        rw [hc]
    _ = _ := ((SegreLiftComap.proof F K ι _ hP' hrel).2).symm

theorem isMultiProjPrime_segreLift (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) :
    IsMultiProjPrime (segreLift ι F W) := by
  have := hW.isPrime
  rw [segreLift_eq_mIdealOver W hW]
  exact isMultiProjPrime_mIdealOver _ (segreJoin_block_ne_zero _ (genPt_block_ne_zero W hW))

end SegreNef

open SegreNef

theorem SegreLiftRelDim.proof_of_segreDim (hD : SegreDim.Statement) : SegreLiftRelDim.Statement := by
  intro F _ K _ _ ι _ W hW
  have := hW.isPrime
  rw [segreLift_eq_mIdealOver W hW,
    hD F K ι _ (ModelGenericPoint.genPt W) (genPt_block_ne_zero W hW),
    ModelGenericPoint.mIdealOver_genPt W hW.multiHomog]

theorem SegreLiftIntNum.proof_of_segreNum (hN : SegreNum.Statement) : SegreLiftIntNum.Statement := by
  intro F _ K _ _ ι _ W hW β
  have := hW.isPrime
  have h := hN F K ι _ (ModelGenericPoint.genPt W) (genPt_block_ne_zero W hW) 1 ![β]
  have hfun : (fun j : Fin 1 => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) (![β] j)) = ![IndefiniteRowSideFullHecke.Kleiman2.pullDeg β] := by
    funext j
    fin_cases j
    rfl
  rw [hfun, ModelGenericPoint.mIdealOver_genPt W hW.multiHomog] at h
  rw [segreLift_eq_mIdealOver W hW]
  exact h

theorem SegreNef.proof_of_lift (hC : SegreLiftRelDim.Statement) (hN : SegreLiftIntNum.Statement) :
    SegreNef.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y _ β
  have h := segreFibresNef_of_map SegreLiftComap.proof (fun F _ K _ _ ι _ W hW => isMultiProjPrime_segreLift W hW)
    hC hN SegreFibreIdeal.proof F Ω F (RingHom.id F) K ι y β
  rw [map_id_ideal, map_id_ideal] at h
  exact h

theorem SegreNef.proof (hD : SegreDim.Statement) (hN : SegreNum.Statement) : SegreNef.Statement :=
  SegreNef.proof_of_lift (SegreLiftRelDim.proof_of_segreDim hD) (SegreLiftIntNum.proof_of_segreNum hN)

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end
