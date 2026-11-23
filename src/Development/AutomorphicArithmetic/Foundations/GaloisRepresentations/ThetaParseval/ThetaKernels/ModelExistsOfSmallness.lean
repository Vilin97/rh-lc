module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelSmallK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldCut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldChart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldSMod
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldMSpec
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.PartCharInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldMCut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinateChangeRealisedWithDoubleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOriginStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairConverse
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.DiagonalColumnInclusion.IncMDiagCols
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxChangeRealisedCompAndReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxChangeIntertwine
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelPf
import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.ResAdm
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.AdelicCoordinatesEvalZeroFormMemAdmissible
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ExistsSchwartzOneCpt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SchrTransl
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplitOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeOfSig
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.EDApply
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.TraceIntMul
import Mathlib.Tactic.Linter.HaveILetI
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.PartCharInvAlt

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AldAscBigT

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald.Asc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PositivityTheory.SiegelWeilFormula.Ald.Asc
namespace PositivityTheory.SiegelWeilFormula.Ald
open Asc in
theorem bigT_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.BigT_k := by
  intro hT _hA F E _ _ _ _ _ σ d dd0 had hrat
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨S0, S0', hS⟩ := GlobalTheory.T.darbouxCoordinateChange_realised_with_double F E σ d.ok.good.cm d.B.ψ hψ (Fin d.m) (Fin d.n ⊕ Fin d.n) d.κ
    (Fin d.m × Fin d.n × Fin 2) _ d.dd dd0 (by exact d.ok.dbl.rat) (by exact hrat)
  have hop := hS.1
  have rhoS : ∀ w, ∀ φ ∈ schA F d.κ, S0 (d.dd.rho d.B.ψ w φ) = dd0.rho d.B.ψ w (S0 φ) := by
    intro w φ hφ
    simp only [Darboux.rho]
    rw [hop.Heisenberg₂ _ _ hφ]
    simp
  have rhoS' : ∀ w, ∀ φ ∈ schA F (Fin d.m × Fin d.n × Fin 2), S0' (dd0.rho d.B.ψ w φ) = d.dd.rho d.B.ψ w (S0' φ) := by
    intro w φ hφ
    have h1 := rhoS w (S0' φ) (hop.pres' φ hφ)
    rw [hop.right φ hφ] at h1
    have hm : d.dd.rho d.B.ψ w (S0' φ) ∈ schA F d.κ :=
      GlobalTheory.EvZeroUniq.schr_mem_schA d.B.ψ hψ _ (hop.pres' φ hφ)
    rw [← h1, hop.left _ hm]
  set l' : ((Fin d.m × Fin d.n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ℂ := d.l ∘ₗ S0' with hl'
  have hadm : l' ∈ (adeleClass F).adm (Fin d.m × Fin d.n × Fin 2) := hop.adm' d.l d.ok.dbl.adm
  have hsurj : ∀ y : Fin d.m × Fin d.n × Fin 2 → AF F, ∃ Z : Mx F E d.m d.n,
      dd0.e (Z * (incM F d.b.1.toCols₁)ᵀ) = (0, y) := by
    intro y
    obtain ⟨Z, X, hw⟩ := eq_split d.b (dd0.e.symm (0, y))
    have h1 := had Z X
    rw [← hw, LinearEquiv.apply_symm_apply] at h1
    have h2 := had Z 0
    rw [Matrix.zero_mul, add_zero, crdB_zero] at h2
    refine ⟨Z, h2.trans ?_⟩
    have h3 := congrArg Prod.snd h1
    simp only at h3
    rw [← h3]
  obtain ⟨t, ht0⟩ := d.ok.frame.2
  have ht : (d.b.1.toCols₁ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) =
      (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * (t.1 : Matrix (Fin d.n) (Fin d.n) E) := ht0
  have hinv : ∀ (y : Fin d.m × Fin d.n × Fin 2 → AF F), ∀ φ ∈ schA F (Fin d.m × Fin d.n × Fin 2),
      l' (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l' φ := by
    intro y φ hφ
    obtain ⟨Z, hZ⟩ := hsurj y
    have e1 : (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = dd0.rho d.B.ψ (Z * (incM F d.b.1.toCols₁)ᵀ) φ := by
      funext x
      simp [Darboux.rho, hZ, schr]
    rw [e1, hl', LinearMap.comp_apply, rhoS' _ φ hφ, LinearMap.comp_apply]
    have e2 : Z * (incM F d.b.1.toCols₁)ᵀ = ((Z * (incM F t.1)ᵀ : Mx F E d.m d.n)) *
        ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)))ᵀ := by
      rw [ht, incM_mul', incM_diagCols, Matrix.transpose_mul]
      exact (Matrix.mul_assoc _ _ _).symm
    rw [e2]
    exact d.ok.dbl.kill _ _ (hop.pres' φ hφ)
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ (Fin d.m × Fin d.n × Fin 2) l' hadm hinv
  have hform : ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = c * S0 Φ (crdB d.bs X) := by
    intro Φ hΦ X
    have hΨ : d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ ∈ schA F d.κ :=
      GlobalTheory.EvZeroUniq.schr_mem_schA d.B.ψ hψ _ hΦ
    have h0 := had 0 X
    rw [Matrix.zero_mul, zero_add] at h0
    simp only [Bf_zero_left] at h0
    have e1 : d.T Φ X = l' (S0 (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ)) := by
      rw [hl', LinearMap.comp_apply, hop.left _ hΨ]
      rfl
    rw [e1, hc _ (hop.pres _ hΨ), rhoS _ _ hΦ]
    simp [Darboux.rho, h0, schr]
  refine ⟨S0, S0', c, ?_, hS, hform⟩
  rintro rfl
  obtain ⟨φ, hφ, hφ0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F d.κ
  have hz : d.T φ = 0 := by
    funext X
    rw [hform φ hφ X, zero_mul]
    rfl
  exact hφ0 (by rw [(hT.1 F E σ d).2.2 φ hφ hz]; rfl)
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldModelPf

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem modelEx_of_k (hS : _root_.PositivityTheory.SiegelWeilFormula.Ald.SDarb_k) (hE : _root_.PositivityTheory.SiegelWeilFormula.Ald.SEv_k) (hB : _root_.PositivityTheory.SiegelWeilFormula.Ald.BigT_k) (hF : SliceFacts) (hO : OpBox) (hU : SubSplit)
    (hC : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k) (hA' : _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k) : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k := by
  intro hT hA F E _ _ _ _ _ σ d n h Y b j hn hs hb hε hj
  obtain ⟨ε, e1, e2⟩ := hε
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨dd0, had0, hr0⟩ := hS F E σ d.B d.bs d.m d.n d.A d.Y d.b ε d.r d.s d.ok.good d.ok.hm d.ok.hn d.ok.sign
    d.ok.frame e1
  obtain ⟨dd', had', hr'⟩ := hS F E σ d.B d.bs d.m n d.A Y b ε d.r d.s d.ok.good d.ok.hm hn hs hb e2
  obtain ⟨hev, hkill, htheta⟩ := hE F E σ d.B d.bs d.m n d.A Y b ε d.r d.s d.ok.good d.ok.hm hn hs hb e2 dd' had'
  obtain ⟨S0, S0', C, hC0, hop, hTf⟩ := hB hT hA F E σ d dd0 had0 hr0
  obtain ⟨c1, c2, c3, c4, -⟩ := hC F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had'
  let dd1 := GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm
  let S1 := GlobalTheory.TowU.RealComp.reix (eK d.m h) ∘ₗ S0
  let S1' := S0' ∘ₗ GlobalTheory.TowU.RealComp.reix (eK d.m h).symm
  have hop1 : GlobalTheory.TowU.IsOp d.B.ψ (fun w => dd1.e (d.dd.e.symm w)) S1 S1' :=
    GlobalTheory.TowU.RealComp.isOp_comp hop.1 (GlobalTheory.TowU.RealComp.isOp_reix d.B.ψ (eK d.m h))
  have hT1 : ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S1 Φ (crdB d.bs X ∘ eK d.m h) := fun Φ hΦ X => by
    rw [hTf Φ hΦ X]
    simp only [S1, LinearMap.comp_apply, GlobalTheory.TowU.RealComp.reix_apply]
    rw [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  have hw := d.ok.dbl.weil
  obtain ⟨om1, hom1⟩ := projHom (G := d.G) (fun x => S1 ∘ₗ d.om x ∘ₗ S1')
    (fun x φ hφ => hop1.pres _ (hw.2.1.pres x _ (hop1.pres' φ hφ)))
    (fun φ hφ => by simp [hop1.right φ hφ])
    (fun x y φ hφ => by
      simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply]
      rw [hop1.left _ (hw.2.1.pres y _ (hop1.pres' φ hφ))])
  have hsp1 : IsUSplitting (adeleClass F) d.B.ψ dd1 (actB (cA σ)) om1 :=
    GlobalTheory.TowU.isUSplitting_of_isOp hψ (fun w => by simp) hop1 hom1 hw.2.1
  have hsr1 : SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) dd1 d.χ
      (diagCols (Fin d.n)) om1 :=
    GlobalTheory.TowU.siegelRule_of_isOp (fun w => by simp) hop1 hom1 hw.2.2
  obtain ⟨hsl1, hsl2, ⟨φ₀, hφ₀, hφ₀0, hφ₀n⟩, -⟩ := hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)
  have hbox := fun g => hO F d.B.ψ hψ _ _ _ _ dd1 d.G (actB (cA σ)) om1 hsp1.toIsSplitting c2 (j g) (c3 g) φ₀ hφ₀ hφ₀0
  let cg : G2 σ Y → ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) :=
    fun g => slice0 _ _ ∘ₗ om1 (j g) ∘ₗ PositivityTheory.ThKF0.Chr.boxL _ φ₀
  have hbx : ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), boxFun φ' φ₀ ∈ schA F (K1 d.m n) := fun φ' hφ' =>
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ' hφ' φ₀ hφ₀
  have hsl0 : ∀ φ' : (Fin d.m × Fin n × Fin 2 → AF F) → ℂ, slice0 _ _ (boxFun φ' φ₀) = φ' := fun φ' => by
    funext x
    simp [slice0, boxFun, hφ₀0]
  have hcg : ∀ g φ', cg g φ' = slice0 _ _ (om1 (j g) (boxFun φ' φ₀)) := fun g φ' => rfl
  have hboxc : ∀ g, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2),
      om1 (j g) (boxFun φ' φ₀) = boxFun (cg g φ') φ₀ := fun g φ' hφ' =>
    (hbox g).2 φ' hφ' φ₀ hφ₀
  obtain ⟨om', hom'⟩ := projHom cg
    (fun g φ' hφ' => hsl1 _ (hsp1.pres _ _ (hbx φ' hφ')))
    (fun φ' hφ' => by rw [hcg, map_one, map_one, Module.End.one_apply, hsl0])
    (fun g g' φ' hφ' => by
      rw [hcg, map_mul, map_mul, Module.End.mul_apply, hboxc g' φ' hφ', hcg g])
  have hboxom : ∀ g, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), om1 (j g) (boxFun φ' φ₀) = boxFun (om' g φ') φ₀ :=
    fun g φ' hφ' => by rw [hom' g φ' hφ', hboxc g φ' hφ']
  have hsp' : IsUSplitting (adeleClass F) d.B.ψ dd' (actB (cA σ)) om' :=
    hU F d.B.ψ hψ _ _ _ _ _ _ dd1 dd' (emb h b d.b) c1 d.G (G2 σ Y) (actB (cA σ)) (actB (cA σ)) j hj.1 c4 om1 om' hsp1
      φ₀ hφ₀ hφ₀0 hφ₀n (fun g => ⟨φ₀, hφ₀, hφ₀0, fun _ _ => rfl, hboxom g⟩)
  have hsg' := hG F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' om1 hsp1.toIsSplitting hsr1 φ₀ hφ₀ hφ₀0 om'
    hboxom
  obtain ⟨S', hS'1, hS'2⟩ := hA' hT F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' S1 S1' C hC0 hop1 hT1
  refine ⟨Fin d.m × Fin n × Fin 2, inferInstance, dd', om', S', ev0 _,
    ⟨hr', ⟨isLagr_diagCols _ _, hsp', hsg'⟩, hS'1, hev, hkill, hS'2, htheta⟩, ?_⟩
  intro Φ hΦ Φ' hΦ' hres g X hX
  have hS1Φ : S1 Φ ∈ schA F (K1 d.m n) := hop1.pres Φ hΦ
  have hsl : Φ' = C • slice0 _ _ (S1 Φ) := by
    funext x
    obtain ⟨X', rfl⟩ := crdB_surj d.bs x
    have e := hres (ext0 h X') (extend_zero_column h X')
    rw [extension_zero_sub, tof_adapted d.bs d.B.ψ had', hT1 Φ hΦ, crdB_eK h d.bs _ (extend_zero_column h X'), extension_zero_sub] at e
    rw [e]
    rfl
  rw [tof_adapted d.bs d.B.ψ had', hom' g Φ' hΦ', hT1 _ (hw.2.1.pres (j g) Φ hΦ), crdB_eK h d.bs X hX]
  have e1' : S1 (d.om (j g) Φ) = om1 (j g) (S1 Φ) := by
    rw [hom1 (j g) _ hS1Φ]
    simp only [LinearMap.comp_apply]
    rw [hop1.left Φ hΦ]
  rw [e1', show (Sum.elim (crdB d.bs (X.submatrix id (em0 h))) 0 : K1 d.m n → AF F) =
    Sum.elim (crdB d.bs (X.submatrix id (em0 h))) 0 from rfl]
  have e2' := congrFun ((hbox g).1 (S1 Φ) hS1Φ) (crdB d.bs (X.submatrix id (em0 h)))
  simp only [slice0, LinearMap.coe_mk, AddHom.coe_mk] at e2'
  rw [e2', hcg, hsl]
  simp only [slice0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [GlobalTheory.SchwartzBox.boxFun_smul_left, map_smul]
  rfl
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilLdexaEv

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
set_option linter.unusedSectionVars false
theorem sEv_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.SEv_k := by
  intro F E _ _ _ _ _ σ B bs m n A Y b ε r s hB hm hn hsg hb hε dd hd
  refine ⟨adelicCoordinatesEvalZeroForm_mem_admissible _, fun z Φ _ => evaluation_zero_unipotent_kill bs A Y b hb dd hd B.ψ z Φ, fun Φ hΦ => ?_⟩
  have hψ : ∀ x : F, B.ψ (algebraMap F (AF F) x) = 1 := hB.std.2.1
  have hs := (summable_of_mem_schA F hΦ).hasSum
  have h := (Equiv.hasSum_iff (xiEquiv (m := m) bs b hb)).mpr hs
  have e1 : thetaSum F Φ = ∑' ξ : Fin m × Fin n × Fin 2 → F, Φ fun i => algebraMap F (AF F) (ξ i) := rfl
  rw [e1]
  convert h using 1
  funext y
  exact evaluation_zero_antisymmetric bs A Y b hb dd hd B.ψ hψ Φ y
end PositivityTheory.SiegelWeilFormula.Ldexa
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldModelW

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem modelEx_wired_k (hD : _root_.PositivityTheory.SiegelWeilFormula.Ald.SDarb_k) (hP : PartCharInv) (hC : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k) : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Ald.modelEx_of_k hD _root_.PositivityTheory.SiegelWeilFormula.Ldexa.sEv_k _root_.PositivityTheory.SiegelWeilFormula.Ald.bigT_k sliceFacts (opBox_of hP sliceFacts) (subSplit_of sliceFacts) hC hG hS
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilLdexaMain

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {m n : ℕ}
theorem sDarb_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.SDarb_k := by
  intro F E _ _ _ _ _ σ B bs m n A Y b ε r s hB hm hn hsg hb hε
  haveI : FiniteDimensional F E := Module.Finite.of_basis bs
  have hσ : ∀ a, σ (σ a) = a := by
    obtain ⟨-, -, -, h⟩ := hB.cm
    intro a
    let τ : E →+* ℂ := Classical.arbitrary _
    apply τ.injective
    rw [h, h, star_star]
  obtain ⟨u, hsym, hεu, hJ⟩ : ∃ u : ℤ, (∀ i j, σ (A.J j i) = (u : E) * A.J i j) ∧ (ε : ℤ) * u = -1 ∧ A.J.det ≠ 0 := by
    rcases hsg with ⟨hA, hY⟩ | ⟨hA, hY⟩
    · refine ⟨1, fun i j => by simp [hA.herm], ?_, GlobalTheory.ThetaRatPair.det_ne_of_sig B A.J hA.sig⟩
      rw [eps_eq hσ Y.J (-1) (fun i j => by simp [hY]) b ε hε hn]
      norm_num
    · refine ⟨-1, fun i j => by simp [hA.skew], ?_, GlobalTheory.ThetaRatPair.det_ne_of_sig' B A.J hA.sig⟩
      rw [eps_eq hσ Y.J 1 (fun i j => by simp [hY]) b ε hε hn]
      norm_num
  have hP := Pm_unit (n := n) σ hσ A.J hJ bs
  let dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2) :=
    ⟨eD σ A.J bs b hP, eD_form σ A.J bs Y.J b ε hε u (fun X Z => Bf_symm hσ A.J u hsym X Z) hεu hP⟩
  have hd : IsAdapted bs A Y b dd := fun Z X => eD_frame σ A.J bs b hP Z X
  refine ⟨dd, hd, fun x => ?_⟩
  obtain ⟨c, hc⟩ := e_rat bs A Y b dd hd x
  exact ⟨_, c, hc⟩
end PositivityTheory.SiegelWeilFormula.Ldexa
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ModelExistsOfSmallness

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem modelExists_of_smallness (hG : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k) : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Ald.modelEx_wired_k _root_.PositivityTheory.SiegelWeilFormula.Ldexa.sDarb_k partCharInv _root_.PositivityTheory.SiegelWeilFormula.Ald.chartFacts_k hG hS
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end
end
