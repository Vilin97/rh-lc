module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.WtDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.AutCrit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.AutMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNearH
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EllCOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EmbProjHolds
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg
import Mathlib.RingTheory.PicardGroup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExistsDual
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExpBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExpDisj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamExOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOfOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOffHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.KaplFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.LadicWeightAtEmbeddingOverPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NearSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NeatLev
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAutRepOfVecFun
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.PevExp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.Pieces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaUnitaryUpperTriangularStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.RFinEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SepPoly
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SqExpH
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SumRep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TopOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TopUpOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TorFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TwistBd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TwistOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.WExpH

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DomOf

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.dom_of :
    UpperTheory.Gal.Wt.Dom := by
  classical
  intro a κ f hf
  have hf' : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ a a κ.natW := hf
  clear hf
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ a a κ.natW] at hf'
  induction hf' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm k
    have h := (Formalism.GradedWeylDivisibility.bidetDominance ℂ a a K sz hsz I m hm).1 k
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm k
    rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
    · exact hx m h k
    · exact hy m h k
  | smul c x _ hx =>
    intro m hm k
    exact hx m (MvPolynomial.support_smul hm) k
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EvLemOf

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.evLem_of :
    UpperTheory.Gal.Wt.EvLem := by
  intro M X Z _ _ _ ev hsep T Φ hT L
  let W : Submodule ℂ (Module.Dual ℂ M) := Submodule.span ℂ (Set.range ev)
  have hbot : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [Submodule.mem_dualCoannihilator] at hm
    exact (Submodule.mem_bot ℂ).2 (hsep m fun x => hm _ (Submodule.subset_span ⟨x, rfl⟩))
  have htop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hbot, Submodule.dualAnnihilator_bot]
  let φ : Module.Dual ℂ M →ₗ[ℂ] (Z → ℂ) :=
    { toFun := fun l z => l (Φ z)
      map_add' := fun a b => by
        ext z
        simp
      map_smul' := fun c a => by
        ext z
        simp }
  have hle : W ≤ T.comap φ := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hT x
  have hL : L ∈ W := by
    rw [htop]
    exact Submodule.mem_top
  exact hle hL
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOfA

section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.famOfA_of :
    UpperTheory.Gal.Wt.AutMul → UpperTheory.Gal.Wt.NrmAut → UpperTheory.Gal.Wt.RFinEx → UpperTheory.Gal.Wt.FamOfA := by
  intro hMul hNrm hR E _ _ _ a τ C hC n hn W ν Q _ f P X
  have hp := fun q => hNrm E a τ C hC n hn (pev (P q)) ((hR a).2 (P q))
  have hd := fun q => hNrm E a τ C hC n hn (fun m => delta ν (X q * m)) ((hR a).1 ν (X q))
  have key : ∀ y₁ y₂ v, famOf n ν f P X y₁ y₂ v =
      ∑ q, ((fun g => pev (P q) (n g * y₂)) * (fun g => delta ν (X q * (n g * y₁)))) * (f q).1 v := by
    intro y₁ y₂ v
    funext g
    rw [famOf_apply, Finset.sum_apply]
    rfl
  refine ⟨fun y₁ y₂ v => ?_, ?_⟩
  · rw [key]
    exact mem_autU.1 (Submodule.sum_mem _ fun q _ => mem_autU.2
      (hMul E a _ _ (hMul E a _ _ ((hp q).1 y₂) ((hd q).1 y₁)) ((f q).2.1 v)))
  · choose S₁ hS₁f hS₁ using fun q => (hp q).2
    choose S₂ hS₂f hS₂ using fun q => (hd q).2
    have hfin : ∀ q, FiniteDimensional ℂ ↥(S₁ q * S₂ q * LinearMap.range (f q).1) := fun q => by
      have h₁ : (S₁ q).FG := Submodule.fg_iff_finiteDimensional _ |>.2 (hS₁f q)
      have h₂ : (S₂ q).FG := Submodule.fg_iff_finiteDimensional _ |>.2 (hS₂f q)
      have h₃ : (LinearMap.range (f q).1).FG := Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
      exact Submodule.fg_iff_finiteDimensional _ |>.1 ((h₁.mul h₂).mul h₃)
    refine ⟨⨆ q, S₁ q * S₂ q * LinearMap.range (f q).1, Submodule.finiteDimensional_iSup _, ?_⟩
    intro y₁ y₂ v
    rw [key]
    exact Submodule.sum_mem _ fun q _ => Submodule.mem_iSup_of_mem q
      (Submodule.mul_mem_mul (Submodule.mul_mem_mul (hS₁ q y₂) (hS₂ q y₁)) (LinearMap.mem_range_self _ v))
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.KaplOf

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.kapl_of :
    UpperTheory.Gal.Wt.KaplFin → UpperTheory.Gal.Wt.Kapl := by
  intro hfin k _ _ Y hY δ ε hδ hε hε1
  have hY' : IsCompact (Y ∩ {x : k | δ ≤ ‖x‖}) :=
    hY.inter_right (isClosed_le continuous_const continuous_norm)
  have hnhds : ∀ c ∈ Y ∩ {x : k | δ ≤ ‖x‖}, Metric.closedBall c (‖c‖ / 2) ∈ nhds c := by
    intro c hc
    have hc' : δ ≤ ‖c‖ := hc.2
    exact Metric.closedBall_mem_nhds c (by linarith)
  obtain ⟨s, hs, hcov⟩ := hY'.elim_nhds_subcover (fun c => Metric.closedBall c (‖c‖ / 2)) hnhds
  obtain ⟨p, h1, h2, h3⟩ := hfin k s δ ε hδ hε hε1 (fun c hc => (hs c hc).2)
  have hbig : ∀ x ∈ Y, δ ≤ ‖x‖ → ‖p.eval x‖ ≤ ε := by
    intro x hx hxδ
    have hmem := hcov ⟨hx, hxδ⟩
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨c, hc, hxc⟩ := hmem
    exact h2 c hc x (by simpa [dist_eq_norm] using hxc)
  refine ⟨p, fun x hx => ?_, hbig, h3⟩
  rcases le_total ‖x‖ δ with h | h
  · exact h1 x h
  · exact (hbig x hx h).trans hε1
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NrmAut

section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.nrmAut_of :
    UpperTheory.Gal.Wt.AutCrit → UpperTheory.Gal.Wt.NrmAut := by
  intro hC E _ _ _ a τ C hCl n hn p hp
  obtain ⟨hpc, A, hAf, hA⟩ := hp
  let S : Submodule ℂ (UA E a → ℂ) := A.map (LinearMap.funLeft ℂ ℂ n)
  have hSf : FiniteDimensional ℂ S := inferInstance
  have hS : ∀ y, (fun g => p (n g * y)) ∈ S := fun y => ⟨_, hA y, rfl⟩
  refine ⟨fun y => ?_, S, hSf, hS⟩
  refine hC E a C hCl _ (fun γ hγ g => by simp only [hn.left γ hγ g])
    (fun c hc g => by simp only [hn.lev c hc g]) (fun g => ?_) S hSf (fun x hx => ?_)
  · have he : (fun x : infU E a => p (n (g * x.1) * y)) =
        fun x : infU E a => p (n g * (cEmb τ x.1 * y)) := by
      funext x
      rw [hn.inf x.1 x.2 g, mul_assoc]
    rw [he]
    exact hpc.comp (continuous_const.mul
      (((GlobalTheory.AutRec.continuous_cEmb_emb τ).comp continuous_subtype_val).mul continuous_const))
  · have he : RU E a x (fun g => p (n g * y)) = fun g => p (n g * (cEmb τ x * y)) := by
      funext g
      change p (n (g * x) * y) = _
      rw [hn.inf x hx g, mul_assoc]
    rw [he]
    exact hS _
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.QROf

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.qR_of :
    UpperTheory.Gal.Wt.QR := by
  intro a y
  obtain ⟨k, hk, b, hg, hb⟩ := GlobalTheory.T.iwasawa_unitary_upper_triangular (y : Matrix (Fin a) (Fin a) ℂ) y.isUnit
  let u : Matrix.unitaryGroup (Fin a) ℂ := ⟨k, hk⟩
  have hu : ((unitaryIncl a u : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = k := rfl
  refine ⟨u, (unitaryIncl a u)⁻¹ * y, ?_, (mul_inv_cancel_left _ _).symm⟩
  have hbm : (((unitaryIncl a u)⁻¹ * y : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = b := by
    rw [Units.val_mul, hg, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  intro i j hij
  rw [hbm]
  exact hb hij
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.LadicWeightEmbeddingOverPlace

section

@[expose] public section

namespace UpperTheory.Gal.Wt

theorem expBasic_holds : ExpBasic := expBasic_of
theorem expDisj_holds : ExpDisj := expDisj_of
theorem evLem_holds : EvLem := evLem_of
theorem pevExp_holds : PevExp := pevExp_of expBasic_holds
theorem dom_holds : Dom := dom_of
theorem sqExp_holds : SqExp := sqExp_h expBasic_holds evLem_holds dom_holds
theorem topUp_holds : TopUp := topUp_of
theorem torFacts_holds : TorFacts := torFacts_of
theorem qR_holds : QR := qR_of
theorem wtBd_holds : WtBd := wtBd_of expBasic_holds expDisj_holds sqExp_holds topUp_holds torFacts_holds
theorem wExp_holds : WExp := wExp_h expBasic_holds sqExp_holds torFacts_holds
theorem rFinEx_holds : RFinEx := rFinEx_of
theorem deltaNear_holds : DeltaNear := deltaNear_h
theorem autCrit_holds : AutCrit := autCrit_of
theorem autMul_holds : AutMul := autMul_of
theorem nrmAut_holds : NrmAut := nrmAut_of autCrit_holds
theorem famOfA_holds : FamOfA := famOfA_of autMul_holds nrmAut_holds rFinEx_holds
theorem sumRep_holds : SumRep := sumRep_of
theorem neatLev_holds : NeatLev := neatLev_of
theorem ellC_holds : EllC := ellC_of
theorem twist_holds : Twist := twist_of autCrit_holds
theorem twistBd_holds : TwistBd := twistBd_of twist_holds
theorem ladic_weight_embedding_over_place : Kap0 := ladic_weight_at_embedding_over_place
theorem kaplFin_holds : KaplFin := kaplFin_of
theorem kapl_holds : Kapl := kapl_of kaplFin_holds
theorem sepPoly_holds : SepPoly := sepPoly_of kapl_holds
theorem nearSub_holds : NearSub := nearSub_of
theorem pieces_holds : Pieces := pieces_of sepPoly_holds nearSub_holds
theorem famOf_holds : FamOf := famOf_of expBasic_holds pevExp_holds sqExp_holds topUp_holds wExp_holds famOfA_holds
theorem famEx_holds : FamEx := famEx_of neatLev_holds ellC_holds twist_holds twistBd_holds ladic_weight_embedding_over_place pieces_holds deltaNear_holds famOf_holds
theorem famProj_holds : FamProj := famProj_of evLem_holds sumRep_holds
theorem famSum_holds : FamSum := famSum_of expBasic_holds evLem_holds torFacts_holds qR_holds wtBd_holds embProj_holds
theorem famWt_holds : FamWt := famWt_of famOff_holds famSum_holds

theorem wtLacEx_holds : UpperTheory.Gal.Int.Cong.WtLacEx := top_of famEx_holds famProj_holds famWt_holds

end UpperTheory.Gal.Wt
end
end
