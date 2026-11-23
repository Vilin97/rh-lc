module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRecGOfIsLocalFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLayerConditionsTrueColumnsLaterStages
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Retie
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EisGEqZeroOfInfinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTiedOfIsRecG
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ResCharThetaJetPlaceDegOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColInJetsIn
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullHermitianColumnsTrueColumns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrderThree
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumnsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeanSquareEvenThetaTwelfthRootInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesAgreeAdelicOfTrueVolumeStatement
public import Formalism.LocalToGlobal.HermitianColumns.HermCols
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas

-- Source module: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WithTrue

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.Mem

def GJStage.withTrue {B : Base} {C : Cols B} (G : GJStage B C) : GJStage B C :=
  letI := B.host.cmStar
  { G with
    vol := fun W => Vol.trueVol B.sp.cm (fun g : Tau B.R => B.host.emb g.1) G.cd W
    vol_pos := fun W => Vol.trueVol_pos B.sp.cm (fun g : Tau B.R => B.host.emb g.1) G.cd W
    gx := Per.trueGx B.host B.embLL B.embE (Equiv.refl _) }

end GlobalTheory.Mem
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterTypePrimesValuesCoefficientFiel

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.PsiRat

theorem natCast_resField_eq_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (h : (p : 𝓞 F) ∈ v.asIdeal) : (p : kv F v) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (v.adicCompletionIntegers F)), IsLocalRing.residue_eq_zero_iff]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))
    (a := (p : v.adicCompletionIntegers F))).2 ?_
  have h1 : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((p : 𝓞 F) : F) := by
    simp
  rw [h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((p : 𝓞 F) : F)
  have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 h
  exact h2.trans_lt h3

theorem range_of_pow_g (B : Base) (i : Fin 2) (z : ℂ) (hz : z ^ B.host.g i = 1) : ∃ r : B.LL, B.embLL r = z := by
  have hp := B.host.g_prime i
  obtain ⟨ζ, -, hζ⟩ := B.roots_Ks (B.host.g i * (B.host.g i - 1)) (by fin_cases i <;> simp)
  have hne : B.host.g i * (B.host.g i - 1) ≠ 0 := mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim := Complex.isPrimitiveRoot_exp _ hne
  have : NeZero (B.host.g i * (B.host.g i - 1)) := ⟨hne⟩
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one (ξ := z) (by rw [pow_mul, hz, one_pow])
  exact ⟨ζ ^ k, by rw [map_pow, hζ, hk]⟩

end GlobalTheory.Mem.Col2.TC.PsiRat


open GlobalTheory.Mem.Col2.TC.PsiRat in
theorem GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g), I.IdG l Z G → ∀ j v h x, ∃ r : B.LL, B.embLL r = G.psi0 j v h x := by
  intro B X I _ _ l Z G _ j v h x
  refine range_of_pow_g B j _ ?_
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have h0 := natCast_resField_eq_zero _ v _ h
  erw [h0]
  rw [zero_mul, AddChar.map_zero_eq_one]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterTypePrimesValuesCoefficientFielStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_psi0_eq_embLL : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g), I.IdG l Z G → ∀ j v h x, ∃ r : B.LL, B.embLL r = G.psi0 j v h x := by
  first | exact @GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField | exact GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField | (intros; apply GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullHermitianColumnsTrueColumnsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_fullHermitianColumns_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (C : ColsTiedSym (I.rec7 l Z)) (g : Formalism.L2.Herm.SymmetricGroupCompatibility (I.rec7 l Z) C.herm.base), I.StdC l Z C → Formalism.L2.Herm.VolumeCompatible (I.rec7 l Z) → ∃ Fu : ColsFullS C, HEq Fu.1.g g ∧ I.StdDt l Z Fu.1.base.dt := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.exists_colsFullS | exact GlobalTheory.Mem.Col2.FullDt.exists_colsFullS | (intros; apply GlobalTheory.Mem.Col2.FullDt.exists_colsFullS <;> assumption)
end
end

-- Source module: Formalism.LocalToGlobal.BesselHermitianTheta.Joints

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Theta

theorem VolTieG.hermVolTied {D : D7} (h : VolTieG D) : Formalism.L2.Herm.VolumeCompatible D := by
  intro W P Q hs hsig μ hμ 𝓕 h𝓕
  exact ((h.volTie W P Q hs hsig).2 μ hμ).2 𝓕 h𝓕

end Formalism.L2.Theta

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGIs

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TrueLocal

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Per GlobalTheory.Glob GlobalTheory.Mem.TruePeriods GlobalTheory.Mem.PeriodTie

theorem omTied_retie_of_cube {D : D7} (hF : FieldOK D.host D.what₂.embLL D.embE) (h3 : ∀ z : ℂ, z ^ 3 = 1 → z ∈ coefM D) {δ : ℂ}
    (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ) : Formalism.L2.GlobalTheoryTheory.OmegaCompatible (retie D) δ := by
  obtain ⟨δ', h', m2, m3⟩ := exists_delta_data D hF
  have h0 := delta_ne_zero h'
  have hu0 : δ / δ' ≠ 0 := div_ne_zero (delta_ne_zero h) h0
  have hu : (δ / δ') ^ 12 = 1 := by
    unfold IsDiscriminantTwelfthRootOfIdealLattice at h h'
    rw [div_pow, h, ← h', div_self (pow_ne_zero _ h0)]
  have hmap : lamOf D D.host.ccK δ = (lamOf D D.host.ccK δ').map (AddMonoidHom.mulLeft (δ / δ')) := by
    rw [lamOf_eq_map, lamOf_eq_map, AddSubgroup.map_map]
    congr 1
    ext; simp [← mul_assoc, div_mul_cancel₀ _ h0]
  generalize δ / δ' = u at hu0 hu hmap
  refine (ties_of_data hF h ?_ ?_).1
  · have e : g2 (lamOf D D.host.ccK δ) = (u ^ 4)⁻¹ * g2 (lamOf D D.host.ccK δ') := by
      unfold g2
      rw [hmap, Model.eisG_map _ _ hu0]; ring
    rw [e]
    exact mul_mem (inv_mem (h3 _ (by rw [← pow_mul, hu]))) m2
  · have e : g3 (lamOf D D.host.ccK δ) = (u ^ 6)⁻¹ * g3 (lamOf D D.host.ccK δ') := by
      unfold g3
      rw [hmap, Model.eisG_map _ _ hu0]; ring
    rw [e]
    refine mul_mem (inv_mem ?_) m3
    rcases sq_eq_one_iff.1 (show (u ^ 6) ^ 2 = 1 by rw [← pow_mul, hu]) with e | e <;> rw [e]
    · exact one_mem _
    · exact neg_mem (one_mem _)

open GlobalTheory.Mem.Top.ColOwe GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC in

theorem omTied_withTrue {B : Base} {C : Cols B} (hF : FieldOK B.host B.embLL B.embE) (hc : B.host.ccK = ⊤) {δ : ℂ}
    (h : Th.IsDiscriminantTwelfthRootOfIdealLattice B.host ⊤ δ) (Z : Later B C) (hZ : Z.G.gx = Per.trueGx B.host B.embLL B.embE (Equiv.refl _)) :
    Formalism.L2.GlobalTheoryTheory.OmegaCompatible (recOf Z) δ := by
  have h1 : IsDiscriminantTwelfthRootOfIdealLattice (recOf Z) (recOf Z).host.ccK δ := by
    have : (recOf Z).host.ccK = ⊤ := hc
    rw [this]; exact h
  have h2 := omTied_retie_of_cube (D := recOf Z) hF (fun z hz => B.fixedField_le_coefficientField (B.KsC_le_LL0C (B.rootsField_le_KsC
    ((le_sup_right.trans le_sup_left : Fld.cycField (3 ^ 4) ≤ Fld.rootsField B.toPre)
      (Fld.mem_cycField (by norm_num) (by rw [show 3 ^ 4 = 3 * 27 by norm_num, pow_mul, hz, one_pow])))))) h1
  obtain ⟨W, V, S, N, G⟩ := Z
  obtain ⟨M, i, e, a, b, c⟩ := h2
  refine ⟨M, i, e, a, b, fun τ => ?_⟩
  obtain ⟨d, hd, hs⟩ := c τ
  refine ⟨d, hd, fun s => ?_⟩
  have : (recOf (⟨W, V, S, N, G⟩ : Later B C)).gx = G.gx := rfl
  rw [this, show G.gx = _ from hZ]
  exact hs s

section Stages

open Formalism.MainNotions.G Formalism.L2.G IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.ConcreteRecord GlobalTheory.Mem.Top.ColOwe GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B}



theorem isLocalFamily_stages (sc : Scale) (Z Z' : Later B C) (L0 : LevelData (recOf Z)) (T : ∀ u, Forms0 (recOf Z) u) (g)
    (h : IsLocalFamily sc (recOf Z) L0 T g) : IsLocalFamily sc (recOf Z') L0 (fun u => forms0Re Z' (T u)) g := by
  run_tac do
    let m ← Lean.Elab.Tactic.getMainGoal
    m.withContext do m.assign (← Lean.Meta.getFVarFromUserName `h)

end Stages

section Main

open Formalism.MainNotions.G Formalism.L2.G IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.ConcreteRecord GlobalTheory.Mem.Top.ColOwe GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC
open Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top.GroupRetwisting

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

theorem companion_of_colsHermS {D : D7} (H : Formalism.L2.Herm.ColsHermS D) : Companion D H.base.lev0 := fun u =>
  have hi : IsIntegral ℤ (D.host.conj ((H.atT u).piU : D.host.E)) :=
    map_isIntegral_int D.host.conj (RingOfIntegers.isIntegral_coe _)
  ⟨Ideal.span {(⟨_, hi⟩ : 𝓞 D.host.E)}, (H.baseL u ⟨_, hi⟩ rfl).1⟩

theorem exists_gTiedS_heq {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (H0 : Formalism.L2.Herm.Herm0 D) (h : H0.lev0 = H.lev0) :
    ∃ g : Formalism.L2.Herm.SymmetricGroupCompatibility D H, HEq g H0.g := by
  obtain ⟨l, g⟩ := H0
  dsimp only at h
  subst h
  exact ⟨g, HEq.rfl⟩

theorem herm0_eq_to0 {D : D7} (X : Formalism.L2.Herm.FullTiedS D) (H0 : Formalism.L2.Herm.Herm0 D) (h : X.base.lev0 = H0.lev0)
    (hg : HEq X.g H0.g) : H0 = X.to0 := by
  obtain ⟨l, g⟩ := H0
  dsimp only at h hg
  subst h
  obtain rfl := eq_of_heq hg
  rfl

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem columnLocalData_of_levelZero_concreteData (w : ColW B f T) (Z : w.Lt) (C : ColsTiedSym (w.D Z)) (hC : TC.StdC w.I w.l Z C)
    (hL : ∀ u, TC.StdLvC w.I w.l Z u (C.forms u)) (hV : Formalism.L2.Herm.VolumeCompatible (w.D Z)) (hO : Formalism.L2.GlobalTheoryTheory.OmegaCompatible (w.D Z) w.I.J.δ)
    (Gt : GatTies (w.D Z)) (c : LatCmp (w.D Z)) (G : GroupCompatibilityAll (w.D Z) Gt c) (hR : IsRecG K.s (w.D Z) Gt c G.herm G.forms)
    (hl : G.herm.lev0 = C.herm.base.lev0) (hf : G.forms = fun u => (C.forms u).to0)
    (hpl : ∀ u v hg (a : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' a)) (x : 𝓞 (w.D Z).host.F),
      x ∈ ((G.herm.g u v hg).pl a).1.asIdeal ↔ (0 : WithTop ℤ) < (w.D Z).what₂.places.val v
        (tauLL (w.D Z) (Gt.gat_pos u v hg ⟨a, s⟩) (algebraMap (w.D Z).host.F (w.D Z).host.E (x : (w.D Z).host.F)))) :
    Nonempty (ColumnDataSplitPrimes K w Z) := by
  obtain ⟨g, hg⟩ := exists_gTiedS_heq C.herm.base G.herm hl
  obtain ⟨Fu, h1, h2⟩ := GlobalTheory.T.exists_fullHermitianColumns_trueColumns w.I w.ok w.pins w.l Z C g hC hV
  have e : Fu.1.base.lev0 = G.herm.lev0 :=
    (congrArg (fun H : Formalism.L2.Herm.ColsHermS (w.D Z) => H.base.lev0) Fu.2).trans hl.symm
  exact ⟨⟨⟨C, hC, hL, Fu, h2, Gt, c, G, herm0_eq_to0 Fu.1 G.herm e (h1.trans hg), hf,
    gPlTiedS_of G.herm hpl _ _ e (h1.trans hg)⟩, hR, hO⟩⟩



theorem nonempty_columnLocalData_of_standardConcreteFamily (w : ColW B f T) (Z : w.Lt) (C : ColsTiedSym (w.D Z)) (hC : TC.StdC w.I w.l Z C)
    (hL : ∀ u, TC.StdLvC w.I w.l Z u (C.forms u)) (g) (hd)
    (h : IsLocalFamily K.s (w.D Z) C.herm.base.lev0 (fun u => (C.forms u).to0) g)
    (hV : Formalism.L2.Herm.VolumeCompatible (w.D { Z with G := { Z.G with gat := g, gat_d := hd } }))
    (hO : Formalism.L2.GlobalTheoryTheory.OmegaCompatible (w.D { Z with G := { Z.G with gat := g, gat_d := hd } }) w.I.J.δ) :
    Nonempty (ColumnDataSplitPrimes K w { Z with G := { Z.G with gat := g, gat_d := hd } }) := by
  obtain ⟨Gt, c, G, hR, hl, hf, hpl⟩ := isRecG_of_isLocalFamily C.joint0
    (fun u => GlobalTheory.T.exists_psi0_eq_embLL w.I w.ok w.pins w.l Z (C.forms u).gl (hC u).gl) hd h
  exact columnLocalData_of_levelZero_concreteData w _ (colsRe _ C) (stdC_colsRe w.I w.l _ C hC) (fun u => stdLvC_colsRe w.I w.l _ C u (hL u)) hV hO Gt c G hR
    (funext hl) (funext fun u => (hf u).trans ((forms0Re_setGat g hd _).symm.trans (columnFormsAlongLaterStages_stageZero_eq _ C u).symm)) hpl



theorem exists_trueVolume_stage_of_any_column_choice (p : WP) : StepW p fun K B f T w => ∃ G : GJStage B w.C, GIs2 K w G := by
  refine StepW.of_all fun K B f T w hO _ _ => ?_
  obtain ⟨Z₀⟩ := TrueColsTest.later w.l (JetEx.hasLetters_of_over hO)
  obtain ⟨C, hC, hL⟩ := GlobalTheory.T.exists_standardColumnComparisons_trueColumns w.I w.ok w.pins w.l Z₀
  obtain ⟨g, hd, h⟩ := exists_isLocalFamily K.s (D := w.D Z₀) (fun u => (C.forms u).to0) C.herm.std (companion_of_colsHermS C.herm)
    C.joint0 fun u => GlobalTheory.T.exists_psi0_eq_embLL w.I w.ok w.pins w.l Z₀ (C.forms u).gl (hC u).gl
  refine ⟨{ Z₀.G.withTrue with gat := g, gat_d := hd }, (LayerTwoModel.gIs2_iff w _).2 fun W V S N => ?_⟩
  have hV : Formalism.L2.Theta.VolTieG (w.D ⟨W, V, S, N, { Z₀.G.withTrue with gat := g, gat_d := hd }⟩) :=
    GlobalTheory.T.volumesAgreeAdelic_of_trueVolume _ fun _ => rfl
  refine ⟨hV, nonempty_columnLocalData_of_standardConcreteFamily w ⟨W, V, S, N, Z₀.G.withTrue⟩ (colsRe _ C) (stdC_colsRe w.I w.l _ C hC)
    (fun u => stdLvC_colsRe w.I w.l _ C u (hL u)) g hd ?_ hV.hermVolTied
    (omTied_withTrue w.fld w.px.ccK_top w.ok.amb_ok.delta _ rfl)⟩
  have h' := isLocalFamily_stages K.s Z₀ ⟨W, V, S, N, Z₀.G.withTrue⟩ _ _ g h
  exact (congrArg (fun F => IsLocalFamily K.s (recOf ⟨W, V, S, N, Z₀.G.withTrue⟩) C.herm.base.lev0 F g)
    (funext (columnFormsAlongLaterStages_stageZero_eq ⟨W, V, S, N, Z₀.G.withTrue⟩ C))).mpr h'

theorem exists_trueVolumeStage_columnChoiceStep : StepW Pinned fun K B f T w => ∃ G : GJStage B w.C, GIs2 K w G := exists_trueVolume_stage_of_any_column_choice Pinned

end Main

end GlobalTheory.Mem.Top.Bl.TrueLocal

end
end
end
