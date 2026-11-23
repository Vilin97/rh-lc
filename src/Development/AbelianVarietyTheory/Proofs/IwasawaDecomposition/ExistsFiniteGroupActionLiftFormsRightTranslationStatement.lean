module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParLevOfQ
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagLiftTranslationMemTypeLevelCharacter
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfMulJ0Decoration
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagLiftTranslationMemTypeLevelCharacterStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.flagLift_translation_mem_typeLevel_character : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
      ∃ hh : (LiftBrg.ActQ.redZ X I U L i t A k κ)⁻¹ *
          Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (LiftBrg.ActQ.redQ X I U L eG i t κ) ∈
          (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
        X.toD7.what₂.embLL (((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨_, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
          (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.ActQ.inv_redZ_mul_g0Hat_type | exact GlobalTheory.Mem.R3.LiftBrg.ActQ.inv_redZ_mul_g0Hat_type | (intros; apply GlobalTheory.Mem.R3.LiftBrg.ActQ.inv_redZ_mul_g0Hat_type <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelGroupReductionOntoFiniteGroupSurjective

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ


theorem redQ_surjective : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (i : Fin X.toD7.R.m) (t : TupU I U), Function.Surjective (LiftBrg.ActQ.redQ X I U L eG i t) := by
  intro X px I U L eG _ _ hL _ i t g
  obtain ⟨c, hc⟩ := hL.is.βV i
  obtain ⟨κ, -, hpar, hr⟩ := GlobalTheory.ParahoricLift.liftsExist (Vc X.toD7 i) (L.βV i) (L.datVt i t) _ _ hc
    (GlobalTheory.StepLifts.places_apart L hL.is t).1 (GlobalTheory.StepLifts.places_apart L hL.is t).2 (eG g)
  refine ⟨⟨(finHom (Vc X.toD7 i)).rangeRestrict κ, ⟨hpar, Subgroup.mem_top _⟩⟩, ?_⟩
  rw [redQ_apply]
  show eG.symm (rTup (L.βV i) (L.datVt i t) (finE (Vc X.toD7 i) κ)) = g
  rw [hr, MulEquiv.symm_apply_apply]

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelGroupReductionOntoFiniteGroupSurjectiveStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.levelGroup_reduction_onto_finite_group_surjective : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (i : Fin X.toD7.R.m) (t : TupU I U), Function.Surjective (LiftBrg.ActQ.redQ X I U L eG i t) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.ActQ.redQ_surjective | exact GlobalTheory.Mem.R3.LiftBrg.ActQ.redQ_surjective | (intros; apply GlobalTheory.Mem.R3.LiftBrg.ActQ.redQ_surjective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdDecoratedLatticeRightTranslateLevelQ

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

theorem castGL_castGL_symm {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (m : GL (Fin b) R) :
    castGL h (castGL h.symm m) = m := by
  subst h
  ext i j
  simp [castGL]

theorem castGL_mem_St_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {a b : ℕ} (h : a = b) (m : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)) (hm : m ∈ Formalism.L2.DIV.St 1) :
    castGL h m ∈ Formalism.L2.DIV.St 1 := by
  subst h
  have e : castGL (rfl : a = a) m = m := by
    ext i j
    simp [castGL]
  rwa [e]

theorem ptS_mul_Q : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) (x : Bridge.Gf (Vc X.toD7 i)),
      LiftBrg.ActQ.ptS X I U i t A k (x * κ) =
        ((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV), (LiftBrg.ActQ.redZ X I U L i t A k κ)⁻¹) • LiftBrg.ActQ.ptS X I U i t A k x := by
  intro X px I U L _ _ hL i t A k hF κ x
  obtain ⟨-, hASt, hAU, hkU, hkSt, -⟩ := hF
  set w : Bridge.Gf (Vc X.toD7 i) → GL (Fin X.B.R.nV) (EA X) := fun g =>
    castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin (Vc X.toD7 i).rank) _)) with hw
  have hwmul : w (x * κ) = w x * w κ := by
    simp only [hw, Subgroup.coe_mul, map_mul]

  have hconj : ∀ g : GL (Fin (Vc X.toD7 i).rank) (EA X), g ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram →
      A⁻¹ * castGL (rkEq X i).symm g * A ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := by
    intro g hg
    refine (hAU _).2 ?_
    have e : A * (A⁻¹ * castGL (rkEq X i).symm g * A) * A⁻¹ = castGL (rkEq X i).symm g := by group
    rw [e, castGL_castGL_symm]
    exact hg
  have hxU : Formalism.UG.bc (swapAE X.toD7) ((x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈
      Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
    obtain ⟨g, hg⟩ := x.2
    rw [← hg]
    exact GlobalTheory.LevFinCong.finE_mem_UA _ g
  have hκP := mem_parLev_of_Q X I U L i t κ
  have hκU := Formalism.L2.DIV.parLev_UA hκP
  have hκS : Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈
      Formalism.L2.DIV.St (1 : GL (Fin (Vc X.toD7 i).rank) (EA X)) := by
    have h0 := Formalism.L2.DIV.parLev_St hκP
    have hb : L.βV i = 1 := hL.beta.1 i
    exact hb ▸ h0
  set y := A⁻¹ * w x * A * k with hy
  set z := (A * k)⁻¹ * w κ * (A * k) with hz
  have hyU : y ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := mul_mem (hconj _ hxU) hkU
  have hzU : z ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := by
    have e : z = k⁻¹ * (A⁻¹ * w κ * A) * k := by rw [hz]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hkU) (hconj _ hκU)) hkU
  have hzS : z ∈ Formalism.L2.DIV.St (1 : GL (Fin X.B.R.nV) (EA X)) := by
    have hwS : w κ ∈ Formalism.L2.DIV.St (1 : GL (Fin X.B.R.nV) (EA X)) := castGL_mem_St_one _ _ hκS
    have hAk := mul_mem hASt hkSt
    exact mul_mem (mul_mem (inv_mem hAk) hwS) hAk
  have hzJ : z ∈ Formalism.L2.Col.J0 X.toD7.sp.cm X.B.R.nV (∅ : Finset (Pl X.toD7.host.E)) :=
    ⟨⟨hzU, hzS⟩, Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)⟩
  have hyz : A⁻¹ * w (x * κ) * A * k = y * z := by
    rw [hwmul, hy, hz]; group
  have hyzU : y * z ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := mul_mem hyU hzU
  have hred : Formalism.L2.Col.redG X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) ⟨z, hzJ⟩ = redZ X I U L i t A k κ := by
    funext v
    show _ = Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) v.1 z
    unfold Formalism.L2.DIV.redFn
    rw [Formalism.L2.DIV.extendOne_of_mem _ hzS]
    rfl
  have hraw := GlobalTheory.Mem.Col2.TopCh.decoRaw_mul_levelIwahori_reduction X.toD7.sp.cm ∅ (sgL X I U t) y z hzJ
  rw [hred] at hraw
  apply Subtype.ext
  show (Formalism.L2.Col.decoOf ∅ (sgL X I U t) (A⁻¹ * w (x * κ) * A * k)).1 =
    (Formalism.L2.Col.decoOf ∅ (sgL X I U t) y).1.act 1 (redZ X I U L i t A k κ)⁻¹
  rw [hyz]
  unfold Formalism.L2.Col.decoOf
  rw [dite_eq_left (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) _ hyzU),
    dite_eq_left (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) _ hyU)]
  exact hraw

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdDecoratedLatticeRightTranslateLevelQStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.stdDecoratedLattice_rightTranslate_levelQ : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) (x : Bridge.Gf (Vc X.toD7 i)),
      LiftBrg.ActQ.ptS X I U i t A k (x * κ) =
        ((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV), (LiftBrg.ActQ.redZ X I U L i t A k κ)⁻¹) • LiftBrg.ActQ.ptS X I U i t A k x := by
  exact @GlobalTheory.Mem.R3.LiftBrg.ActQ.ptS_mul_Q
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupActionLiftFormsRightTranslation

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2


noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

theorem formRho_one_apply {Xf : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 Xf.E))}
    (C : Formalism.L2.Col.CoefPk Xf n (Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG))) (Λ : Formalism.L2.Col.LevFam Xf.E Xf.K n SG)
    (h : Λ.grp) (v : C.V) :
    Formalism.L2.Col.formRho C Λ ((1 : Formalism.L2.Col.UF Xf.E n), h) v = ((Λ.chr h : Xf.Kˣ) : Xf.K) • v := by
  show (((Λ.chr h : Xf.Kˣ) : Xf.K) • C.rho 1) v = _
  rw [map_one]
  rfl


theorem act_key (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U)
    (A k : GL (Fin X.B.R.nV) (EA X)) (P : PresL X I hX U Xg tr L cV i t)
    (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q)
    (h : Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.nV) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
    (hh : h ∈ (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp)
    (hpt : ∀ x : Bridge.Gf (Vc X.toD7 i), ptS X I U i t A k (x * κ) =
      ((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
        h * (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
        ptS X I U i t A k x)
    (hch : X.toD7.what₂.embLL (((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨h, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
      (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ))
    (φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (x : Bridge.Gf (Vc X.toD7 i)) :
    P.coef (((Formalism.L2.Col.unipotentRightActionFormsV X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1) (redQ X I U L eG i t κ) φ :
      (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) :
        (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V)
        (ptL X I U i t A k x)) =
      (((envL X I hX U Xg tr L cV i t).lev.ch κ)⁻¹ : ℂˣ) •
        P.coef ((φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
          (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V) (ptL X I U i t A k (x * κ))) := by
  have h1 := φ.2 (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV), ⟨h, hh⟩) :
      Formalism.L2.Col.FormG (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv)
      (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
          (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
          ptS X I U i t A k x)
  have h2 : (φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
      (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V) (ptS X I U i t A k (x * κ)) =
      ((((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨h, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K)) •
        (φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
          (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V)
        (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
          (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
          ptS X I U i t A k x) := by
    rw [hpt x, ← one_mul (1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV), ← Prod.mk_mul_mk, mul_smul]
    exact h1.trans (formRho_one_apply _ _ _ _)
  refine Eq.trans (congrArg P.coef (Formalism.L2.Col.trRep_apply _ _ _ _ _ φ _)) ?_
  have h3 : P.coef ((φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
      (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V) (ptS X I U i t A k (x * κ))) =
      (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ) •
        P.coef ((φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
          (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V)
        (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
          (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
          ptS X I U i t A k x)) := by
    rw [h2]
    refine (P.coef.map_smulₛₗ _ _).trans ?_
    rw [hch]
  exact (inv_smul_smul ((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ) _).symm.trans (congrArg _ h3.symm)

theorem lemT : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
      ∃ h : Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.nV) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1),
        ∃ hh : h ∈ (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
          (∀ x : Bridge.Gf (Vc X.toD7 i), LiftBrg.ActQ.ptS X I U i t A k (x * κ) =
            ((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
              h * (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (LiftBrg.ActQ.redQ X I U L eG i t κ))⁻¹) •
              LiftBrg.ActQ.ptS X I U i t A k x) ∧
          X.toD7.what₂.embLL (((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨h, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
            (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ) := by
  intro X px I U L eG hI hV hL hG i t A k hA κ
  obtain ⟨hh, hc⟩ := GlobalTheory.T.flagLift_translation_mem_typeLevel_character X px I U L eG hI hV hL hG i t A k hA κ
  refine ⟨_, hh, fun x => ?_, hc⟩
  rw [GlobalTheory.T.stdDecoratedLattice_rightTranslate_levelQ X px I U L hI hV hL i t A k hA κ x, mul_inv_cancel_right]


theorem lemAct : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    ∀ (g : Gc X.B px) (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q), LiftBrg.ActQ.redQ X I U L eG i t κ = g →
      ∀ f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms,
        P.ext ((((famR X I hX U Xg tr).A.leftGroupActionLift i t g f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms)) : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V) =
          Bridge.g0Act (LiftBrg.envL X I hX U Xg tr L cV i t).lev.ch κ (P.ext (f : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t A k hA P hP g κ hκ f
  obtain ⟨h, hh, hpt, hch⟩ := lemT X px I U L eG hI hV hL hG i t A k hA κ
  subst hκ
  funext x
  have e1 := hP ((famR X I hX U Xg tr).A.leftGroupActionLift i t (redQ X I U L eG i t κ) f) x
  have e2 := hP f (x * κ)
  unfold Bridge.g0Act
  refine e1.trans ?_
  refine Eq.trans ?_ (congrArg (fun w => (((LiftBrg.envL X I hX U Xg tr L cV i t).lev.ch κ)⁻¹ : ℂˣ) • w) e2).symm
  have e3 : (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm
      ((famR X I hX U Xg tr).A.leftGroupActionLift i t (redQ X I U L eG i t κ) f)) =
      Formalism.L2.Col.unipotentRightActionFormsV X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1) (redQ X I U L eG i t κ)
        (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm f) :=
    LinearEquiv.symm_apply_apply _ _
  rw [e3]
  exact act_key X I hX U Xg tr L eG cV i t A k P κ h hh hpt hch _ x

theorem exists_actTie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    ∃ a : Bridge.ActTie (Bridge.ratF (Vc X.toD7 i)) P (LiftBrg.envL X I hX U Xg tr L cV i t).lev.Q
        (LiftBrg.envL X I hX U Xg tr L cV i t).lev.ch ((famR X I hX U Xg tr).A.leftGroupActionLift i t),
      ∀ q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
        eG (a.red q) = rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL _ _)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t A k hA P hP
  refine ⟨{ red := redQ X I U L eG i t
            red_surj := GlobalTheory.T.levelGroup_reduction_onto_finite_group_surjective X px I U L eG hI hV hL hG i t
            red_ker := fun q => redQ_eq_one_iff X I U L eG i t q
            act_eq := lemAct X px I hX U Xg tr L eG hI hV hL hG cV i t A k hA P hP }, fun q => ?_⟩
  exact eG_redQ X I U L eG i t q

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupActionLiftFormsRightTranslationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.exists_finiteGroupAction_liftForms_rightTranslation : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    ∃ a : Bridge.ActTie (Bridge.ratF (Vc X.toD7 i)) P (LiftBrg.envL X I hX U Xg tr L cV i t).lev.Q
        (LiftBrg.envL X I hX U Xg tr L cV i t).lev.ch ((famR X I hX U Xg tr).A.leftGroupActionLift i t),
      ∀ q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
        eG (a.red q) = rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL _ _)) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.ActQ.exists_actTie | exact GlobalTheory.Mem.R3.LiftBrg.ActQ.exists_actTie | (intros; apply GlobalTheory.Mem.R3.LiftBrg.ActQ.exists_actTie <;> assumption)
end
end
