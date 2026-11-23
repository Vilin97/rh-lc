module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FerreroWashington
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AdmissibleOfPageN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountIV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountVs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.FinalLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PointArith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SumOut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostCond
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOfLemmaK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.TorsClass
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ZqField
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVFinalU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocPublished
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THidaU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ThmBcOfPsiBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.PfromAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.OverIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.EigV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PrimCase
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountZ

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.countZ :
    PropZ → CountZ := by
  intro hZ χ
  refine ⟨0, fun h _ t hB Ω _ _ _ l hl c e hl2 he0 het ψ hψ hc => ?_⟩
  obtain ⟨hnB, hdiv, rfl⟩ := hc
  have h5 : 5 ≤ l := by
    have h3 : l ≠ 3 := fun h3 => hnB (h3 ▸ Finset.mem_insert_self _ _)
    have h4 : l ≠ 4 := fun h4 => absurd (h4 ▸ hl.out) (by norm_num)
    have := hl.out.two_le
    omega
  have hev : Even e := by
    have h1 := (h.mem_X.1 hψ).2
    unfold PsiEven at h1
    rw [MulChar.one_apply (isUnit_one.neg)] at h1
    by_contra hne
    rw [(Nat.not_even_iff_odd.1 hne).neg_one_pow] at h1
    have h2 : (2 : c.O) = 0 := by linear_combination h1
    exact two_ne_zero h2
  have h2e : 2 ≤ e := by obtain ⟨k, rfl⟩ := hev; omega
  have hd : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O h.N) = 1 := by
    ext σ
    simp [Chr.dirG]
  have h0 : Vlen Ω c e (1 : DirichletCharacter c.O h.N) = 0 := by
    unfold Vlen
    rw [hd]
    exact le_antisymm ((Chr.V'_le_V l h.N e 1).trans (hZ Ω l c e h5 h2e hev hdiv).le) bot_le
  refine ⟨by rw [h0]; simp, ?_⟩
  simp [Vn, h0, Chr.nrm]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ThmHV

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.thmHV :
    PointHV → ∀ (K : BConst) (Ct : ℝ), 0 < Ct → ThmHV K Ct := by
  intro hP K Ct hCt ψ
  obtain ⟨C, r₁, r₂, hr₁, hr₂, hmain⟩ := hP ψ (fun l => Nat.log l (K.Rl l (Lchi ψ l)) + 3)
  refine ⟨(C : ℝ), r₁, r₂, hr₁, hr₂, ?_⟩
  intro eps A1 heps _
  have hJ : 0 < Jchi K Ct eps ψ := BConst.J_pos K hCt heps _ _ _
  refine ⟨(2 : ℝ) ^ Jchi K Ct eps ψ, ?_⟩
  intro e t hadm X hX q d hpair hq hd hlist _ Y hwin x hYx hxY
  obtain ⟨⟨hXY, hYX⟩, hwin'⟩ := hwin
  have hXY' : X ^ (1 / Jchi K Ct eps ψ) ≤ Y := hXY
  have h1 : ((2 : ℝ) ^ Jchi K Ct eps ψ) ^ (1 / Jchi K Ct eps ψ) ≤ X ^ (1 / Jchi K Ct eps ψ) :=
    Real.rpow_le_rpow (by positivity) hX (by positivity)
  rw [one_div, Real.rpow_rpow_inv (by norm_num) hJ.ne'] at h1
  rw [one_div] at hXY'
  have hx2 : (2 : ℝ) ≤ x := by linarith
  obtain ⟨he2, -, ht2, htx⟩ := hadm x hx2
  have hxX : x ≤ X := le_trans hxY hYX
  have htX : (t x : ℝ) ≤ X ^ Ct := le_trans htx (Real.rpow_le_rpow (by linarith) hxX hCt.le)
  intro E _ _ _ hE
  have hB := hwin' x hYx hxY
  have hq' : 2 * t x + 1 < q := by exact_mod_cast (show (2 * (t x : ℝ) + 1) < q by linarith)
  have hd' : 2 * t x + 1 < d := by exact_mod_cast (show (2 * (t x : ℝ) + 1) < d by linarith)
  have hbig : Host.Big ⟨ψ, e x, q, d, he2, hpair⟩ (t x) := by
    refine ⟨hq', hd', ?_⟩
    intro y hy
    apply hlist y
    simp only [Host.q, Host.o, List.mem_cons, List.not_mem_nil] at hy ⊢
    tauto
  have key := hmain ⟨ψ, e x, q, d, he2, hpair⟩ rfl
    (hlist r₁ (by simp)).1 (hlist r₁ (by simp)).2 (hlist r₂ (by simp)).1 (hlist r₂ (by simp)).2
    (t x) ht2 hbig (Real.exp (x ^ (4 * eps / 5))) (Real.exp_pos _).le
    (fun l hl _ => hB.2 l hl) E hE
  rw [hostCond ⟨ψ, e x, q, d, he2, hpair⟩ E hE]
  simpa [Real.rpow_natCast] using key
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.JointWinOfCounts

section

@[expose] public section

open Formalism.GaloisCohomology UpperTheory.Top

namespace UpperTheory.V.HV

theorem pointHV_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV) (hZ : CountZ) : PointHV :=
  point (sumIn h2 h5 (countVs hP hF hT CK hK) countIV) (sumOut h1 hZ h2 h3)

theorem thmHV_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV) (hZ : CountZ) (K : BConst) {Ct : ℝ}
    (hC : 0 < Ct) : ThmHV K Ct :=
  thmHV (pointHV_of_counts hP hF hT hK h1 h2 h3 h5 hZ) K Ct hC

theorem jointWin_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) {K : BConst} (hB : ThmBab K 401) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV)
    (hZ : CountZ) : JointWin 401 :=
  jointWin_of (by norm_num) hB (thmHV_of_counts hP hF hT hK h1 h2 h3 h5 hZ K (by norm_num))

theorem vwin_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) {K : BConst} (hB : ThmBab K 401) (hc : ThmBcFree) (h1 : CountI) (h2 : CountII) (h3 : CountIII)
    (h5 : CountV) (hZ : CountZ) : VWin :=
  vwin_of_joint (jointWin_of_counts hP hF hT hK hB h1 h2 h3 h5 hZ) ((thmBc_iff (by norm_num)).2 hc)

end UpperTheory.V.HV
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.PropZ

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

theorem UpperTheory.V.X.propZ :
    HV.PropZ := by
  intro Ω _ _ _ l _ c e h5 h2 hev hd
  by_cases h : l - 1 ∣ e
  · exact UpperTheory.V.X.zOne Ω l c.O (by omega) e (by omega) h
  · exact UpperTheory.V.X.zQuad Ω l c.O h5 e hev hd h
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PsiOf

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.psiOf :
    Rec → PsiBound := by
  intro hR E Ω _ _ _ _ _ _ _ _ _ _ N _ ρ hρ l _ hl2 hlE O _ _ e he ψ hodd a ha
  haveI : IsGalois ℚ E := inferInstance
  let c : HV.Coef l := ⟨O, inferInstance, inferInstance⟩
  let ψ' : DirichletCharacter (↥c.O) N := MulChar.ofUnitHom (ψ.comp ρ)
  have hcomp : MulChar.ringHomComp ψ' c.O.val.toRingHom = chiOf ρ ψ := by
    ext b
    simp [ψ', chiOf, MulChar.ringHomComp_apply]
  have hord : ¬ l ∣ orderOf ψ' := by
    intro hdiv
    apply hlE
    refine hdiv.trans ?_
    rw [← IsGalois.card_aut_eq_finrank]
    apply orderOf_dvd_of_pow_eq_one
    ext b
    simp only [ψ', MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, MulChar.one_apply_coe]
    have h2 : ψ (ρ b) ^ Fintype.card Gal(E/ℚ) = 1 := by
      rw [← map_pow, pow_card_eq_one, map_one]
    have h3 := congrArg (fun u : (↥O)ˣ => ((u : ↥O) : PadicAlgCl l)) h2
    simpa using h3
  have hodd' : ψ' (-1) = (-1) ^ (e + 1) := by
    have h1 := congrArg (fun χ => χ (-1)) hcomp
    simp only [MulChar.ringHomComp_apply] at h1
    apply Subtype.val_injective
    rw [hodd] at h1
    simpa using h1
  have key := vChar hR Ω l c hl2 N ψ' e he hord hodd' a (by rw [hcomp]; exact ha)
  obtain ⟨_, hker, hlift⟩ := galQuot ℚ E Ω
  have hρσ : ∀ σ : G ℚ Ω, ρ (Chr.cls ℚ Ω N σ) = AlgEquiv.restrictNormalHom E σ := by
    intro σ
    have h1 := hρ (Chr.cls ℚ Ω N σ) σ.toRingEquiv (fun x hx => Chr.cls_spec N σ x hx)
    have h2 := hlift σ
    ext x
    apply (algebraMap E Ω).injective
    exact (h1 x).symm.trans (h2 x)
  have hdir : Chr.dirG ℚ Ω ψ' = ψ.comp (AlgEquiv.restrictNormalHom E) := by
    ext σ
    simp [Chr.dirG, ψ', hρσ]
  obtain ⟨_, hopen, hidx⟩ := galEmbTop ℚ E Ω
  haveI : (galOf ℚ E Ω).Normal := by
    rw [← hker]
    infer_instance
  have hle : galOf ℚ E Ω ≤ (ψ.comp (AlgEquiv.restrictNormalHom E)).ker := by
    rw [← hker]
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [hg]
  have heig := Chr.eigV ℚ Ω l O e (ψ.comp (AlgEquiv.restrictNormalHom E)) (galOf ℚ E Ω) hopen hle
    (by rw [hidx]; exact hlE)
  have hpsi : psiLen Ω e ψ = Chr.eigL l e (galOf ℚ E Ω) (ψ.comp (AlgEquiv.restrictNormalHom E)) := rfl
  rw [hpsi, heig, ← hdir]
  exact key
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Iv

section

@[expose] public section

theorem UpperTheory.V.ML.iv :
    GlobalTheory.Published.PoitouTateDuality → ReciprocityTheory.Gal.UnramifiedOrthogonality → UpperTheory.V.Odd.PsiBound :=
  fun h₁ h₂ => UpperTheory.V.ML.psiOf (UpperTheory.V.ML.recip h₁ h₂)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVCore

section

@[expose] public section




section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.HV.Core
open UpperTheory.V.Lit UpperTheory.V.W
theorem of_four_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hK : ∃ CK : ℝ, LemmaK CK) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV) : VWin := by
  obtain ⟨B, hB⟩ := Win.thmBab_of_lemmaK (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK FW.ferreroWashington hK
  obtain ⟨CK, hL⟩ := hK
  exact vwin_of_counts (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK hL (hB 401 (by norm_num))
    (Odd.thmBcFree_of (ML.iv (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.uo)) h1 h2 h3 h5 (countZ X.propZ)
theorem modU_of_printsH (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.W.ModUAlt := _root_.UpperTheory.V.W.modularity_unitary_of_automorphy_hida_unitary hH.litN Pa.pFromAut (_root_.UpperTheory.V.Hi.hida_unitary_of_printed_hida hH)
end UpperTheory.V.HV.Core
end
end
end
