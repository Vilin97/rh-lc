module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwChainWtSharpDivDe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
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
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawTopLevelStabilizerStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelLawOfFiniteDatumLawStatement
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeOneAddPrimeSmulEqOne
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumInvariantCBHomTwistPrimes

section

@[expose] public section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory.TopXiInvQ

open Formalism.L2.Col.LocE Formalism.L2.Col.Loc GlobalTheory.GO

theorem phiTopG_add {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (sharp : Bool) (i : ℕ) (hc : cOf R i = 0) (P : HeightOneSpectrum (𝓞 X.E))
    (x z : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0))
    (hz : ∀ s l, IntAt P (z (Pi.single s 1) l / (qOf P : X.E))) :
    PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P (x + z) = PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x := by
  unfold PhiTopG
  split_ifs
  · exact GlobalTheory.TopInv.PhiGS_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ _ _ _ _ hc x z hz
  · exact GlobalTheory.TopInv.PhiG_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ _ _ _ _ hc x z hz
  · exact GlobalTheory.TopInv.PhiQ_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ hc x z hz

theorem xiTop_invQ : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) x z, Y ∈ ybSet sel mu cst p.deco.1.N → z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst (m2 + 1) p Y p' (x + z) = XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  intro X Pr R Ch sel S mu cst L G m2 _hX hPr _hsel _hg _hT hL u p Y p' x z hY hz
  have hc := hL.cst_ok
  have hm := hL.hm
  have hc0 : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  obtain ⟨h1, h2⟩ := loc_of_mem_mulLat (cst := cst) hPr p p' x hz
  rw [XiTop_eq, XiTop_eq, h1]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have hq0 := GlobalTheory.TopInv.qOf_ne P.1
  rw [GlobalTheory.TopInv.inFr_add]
  have hZ := h2 P
  generalize inFr (frsF sel mu p P) (frsF sel mu p' P) z = Z at hZ ⊢
  unfold topDat
  rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
  refine congrArg₂ (· * ·) (phiTopG_add Ch mu _ (m2 + 1) hc0 P.1 _ _ fun s l => ?_)
    (GlobalTheory.TopInv.ftY_add sel mu cst hc P (hL.depthQ P) _ _ _ (fun s => ?_) fun l => ?_)
  · obtain ⟨s, rfl⟩ : ∃ t, s = Fin.castAdd _ t := ⟨⟨s.1, by have := s.2; omega⟩, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, GlobalTheory.TopStep.castAdd_single, ← pow_one (qOf P.1 : X.E)]
    refine GlobalTheory.TopInv.intAt_div_pow_le hq0 hc.B_pos ?_
    rw [div_eq_inv_mul]
    exact hZ s _
  · refine GlobalTheory.TopInv.atNL_int _ _ _ fun l => ?_
    rw [div_eq_inv_mul]
    exact hZ s l
  · have h3 := GlobalTheory.TopInv.repY_mem sel mu cst _ _ hY P
    rw [← (frsF sel mu p P).apply_symm_apply (_ • _)] at h3
    replace h3 := (GlobalTheory.TopStep.frsF_mem p P _).1 h3
    rw [map_smul] at h3
    exact (mem_localization_standardLattice _ _).1 h3 l

end GlobalTheory.TopXiInvQ
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumInvariantCBHomTwistPrimesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical

theorem _root_.GlobalTheory.T.lastStep_datum_invariant_cB_hom_twist_primes : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) x z, Y ∈ ybSet sel mu cst p.deco.1.N → z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst (m2 + 1) p Y p' (x + z) = XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  first | exact @GlobalTheory.TopXiInvQ.xiTop_invQ | exact GlobalTheory.TopXiInvQ.xiTop_invQ | (intros; apply GlobalTheory.TopXiInvQ.xiTop_invQ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiCpl1Stab

section

@[expose] public section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory.StabLaw

section
variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem rhoS_one (i : ℕ) (P : rowSG Pr sel mu) : rhoS Ch sel mu i P 1 = 1 := by
  unfold rhoS LocE.unitV
  simp [TopStep.reduction_one₂]
end

theorem xiCpl1_stab : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → ∀ (u : Pr.Word) (al : L.β m2) (b : L.β (m2 + 1)) (p : ChPt (R := R) sel mu u m2) (p' : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (a : FrmG (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b)), Y ∈ ybSet sel mu cst p'.deco.1.N → a • p' = p' → (fun v => a.1.1 v) '' Y = Y → ∀ x, XiCpl1 Ch sel mu cst L m2 al p p' Y (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst m2 P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((L.levG (m2 + 1) b).chr a.2.1 * (L.levQ (m2 + 1) b).chr a.2.2 : X.Kˣ) : X.K) * XiCpl1 Ch sel mu cst L m2 al p p' Y x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hg hT hL _ _ _ _ u al b p p' Y a hp1 hfix hY x
  have hd := (TopStep.tilOk_of_avoid (mu := mu) hPr hsel u ⟨hT u, hg⟩).2.2
  obtain ⟨κ', a', hκ', ha', ea'⟩ := TopLaw.exists_pass hd a p'
  have hp2 : (fun v => a.1.1 v) '' Y ∈ ybSet sel mu cst (a • p').deco.1.N := (ybSet_gmap sel mu cst _ a.1.1 Y).2 hp1
  have ha : ∀ P, TopLaw.LevAt (L.levG m2 al) (L.levQ m2 al) P ((1 : GLQ X.E (R.N m2) (rowSG Pr sel mu)) P) ((fun _ => 1 : rowSG Pr sel mu → X.Kˣ) P) := by
    intro P
    refine ⟨fun hP => ?_, fun hQ hP => ?_⟩
    · refine ⟨by rw [Pi.one_apply, map_one]; exact one_mem _, ?_⟩
      exact (map_one _).symm.trans (congrArg _ (Subtype.ext (map_one _).symm))
    · exact ⟨one_mem _, (map_one _).symm⟩
  have hκ : ∀ P, frsF sel mu ((1 : FrmG (L.levG m2 al) (L.levQ m2 al)) • p) P =
      (1 : UF X.E (R.N m2)).1 * (frsF sel mu p P * (((1 : GLQ X.E (R.N m2) (rowSG Pr sel mu)) P)⁻¹).1) := fun P => by
    rw [one_smul]; simp
  have law := CoupledLaw.xiCpl1_law (G := G) (q := (1 : FrmG (L.levG m2 al) (L.levQ m2 al)) • p) hX hPr hL hp1 hp2 hκ hκ' ha ha' x
    (TopLaw.phiT_act _ _ _ _ _ _ _)
  rw [one_smul, hfix, hY] at law
  rw [hfix] at hκ'
  have hdet : ∀ P, (LinearEquiv.det a.1.1 : X.Eˣ) = LinearEquiv.det (κ' P).1 := fun P => by
    have h := congrArg LinearEquiv.det (hκ' P)
    rw [map_mul, map_mul, InvMemClass.coe_inv, map_inv] at h
    rw [mul_left_comm] at h
    exact mul_inv_eq_one.mp (mul_left_cancel (h.symm.trans (mul_one _).symm))
  have hprod : ∀ P, muAt Ch sel mu cst m2 P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) =
      rhoS Ch sel mu m2 P ((LinearEquiv.det ((1 : GLQ X.E (R.N m2) (rowSG Pr sel mu)) P).1 : X.Eˣ) : X.E) *
        rhoT Ch sel mu m2 P ((LinearEquiv.det (κ'⁻¹ P).1 : X.Eˣ) : X.E) := fun P => by
    rw [hdet P, MatLaw.muAt_det, Pi.inv_apply, TopLaw.rhoT_inv, Pi.one_apply, OneMemClass.coe_one, map_one,
      Units.val_one, rhoS_one, one_mul]
  have e : x ∘ₗ ((1 : UF X.E (R.N m2)) : Sp X.E (R.N m2) ≃ₗ[X.E] Sp X.E (R.N m2)).symm.toLinearMap = x :=
    LinearMap.ext fun v => rfl
  rw [e, Finset.prod_const_one, inv_one, inv_one, mul_one, ea'] at law
  rw [Finset.prod_congr rfl fun P _ => hprod P]
  exact law

end GlobalTheory.StabLaw
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiEntryStab

section

@[expose] public section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical
open Formalism.L2.Ker GlobalTheory.TopStep GlobalTheory.TopLaw GlobalTheory.MatLaw

noncomputable section

namespace GlobalTheory.FiLaw

theorem xiEntry_stab : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → ∀ (u : Pr.Word) (i : ℕ), i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) (a : FrmG (L.levG (i + 1) be) (L.levQ (i + 1) be)), a • p' = p' → ∀ x, XiEntry Ch sel mu cst L i al be p p' (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst i P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((L.levG (i + 1) be).chr a.2.1 * (L.levQ (i + 1) be).chr a.2.2 : X.Kˣ) : X.K) * XiEntry Ch sel mu cst L i al be p p' x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hg hT hL _ _ _ _ u i hi al be p p' a ha x
  have hd := (tilOk_of_avoid (mu := mu) hPr hsel u ⟨hT u, hg⟩).2.2
  obtain ⟨κ, c, hκ, hc, ec⟩ := exists_pass hd (1 : FrmG (L.levG i al) (L.levQ i al)) p
  obtain ⟨κ', c', hκ', hc', ec'⟩ := exists_pass hd a p'
  have key := xiEntry_law hX hPr hsel hL hi hκ hκ' hc hc' x (phiT_act _ _ _ _ _ _ _)
  have e1 : x ∘ₗ ((1 : FrmG (L.levG i al) (L.levQ i al)).1.1.symm.toLinearMap) = x := LinearMap.ext fun v => rfl
  rw [one_smul, ha, e1, ec, ec'] at key
  simp only [Prod.snd_one, Prod.fst_one, map_one, mul_one, inv_one] at key
  rw [← key]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have h1 : ((κ P)⁻¹).1 = 1 := by
    have h := hκ P
    rw [one_smul] at h
    simpa using h
  have h2 : LinearEquiv.det (κ' P).1 = LinearEquiv.det a.1.1 := by
    have h := congrArg LinearEquiv.det (hκ' P)
    rw [ha, map_mul, map_mul, Subgroup.coe_inv, map_inv] at h
    rw [mul_left_comm] at h
    have h' := mul_left_cancel (h.symm.trans (mul_one _).symm)
    exact (mul_inv_eq_one.1 h').symm
  rw [Pi.inv_apply, Pi.inv_apply, h1, map_one, Units.val_one, rhoT_inv, ← muAt_det, h2]
  unfold rhoS
  rw [GlobalTheory.Mem.Col2.IdxEx.Cong.unitV_one, one_mul]

end GlobalTheory.FiLaw
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassSumTermLawStabiliserTarget

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ

theorem gmap_of_fix {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {Λ : LevFam X.E X.K n SG}
    {Θ : LevQFam X.E X.K n Q} (a : FrmG Λ Θ) (p : DecoF X.E n ST SG Q) (h : a • p = p) :
    gmap a.1.1 p.deco.1.N = p.deco.1.N :=
  congrArg (fun q : DecoF X.E n ST SG Q => q.deco.1.N) h

theorem mulLat_mul_le {E : Type} [Field E] [NumberField E] {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (a b : ℕ)
    (M : Submodule (𝓞 E) H) : mulLat (a * b) M ≤ mulLat b M := by
  rintro z ⟨w, hw, rfl⟩
  refine ⟨((a : 𝓞 E)) • w, M.smul_mem _ hw, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, Nat.cast_mul, mul_comm]

theorem term_law : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → ∀ u μ (G : StabDat (D.chTw u μ)), StabPin t u μ G → ∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw (t.O u μ) i c c' g := by
  intro D L hT Gi Gl K Y cX ex t hC u μ G hG i hi c c' g hg
  have hok := t.idx_ok μ
  have hm := hok.hm
  obtain ⟨hSS, hlev, -⟩ := t.rd_chain u μ
  obtain ⟨pt, ix, yb, pT, hN, hyb, hE, hC1, hTop, hGi, hGm, hGT⟩ := hG
  have dat := GlobalTheory.T.pairKernelLaw_of_finiteDatumLaw D L hT Gi Gl K Y cX ex t hC.fields hC.sel hC.bad.1 hC.bad.2.1 hC.bad.2.2.1 hC.bad.2.2.2 hC.chars u μ i hi c c'
  have fin : ∀ (f : HomE t.X.E (D.R.N i) (D.R.N (i + 1)) → t.X.K) (N : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)))
      (N' : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N (i + 1)))) (γ : UF t.X.E (D.R.N (i + 1))) (k : t.X.K),
      (t.rd u μ).N i c = N → (t.rd u μ).N (i + 1) c' = N' → (∀ x, (t.rd u μ).Xi i c c' x = t.seam.σ₀ (f x)) →
      gmap γ.1 N' = N' →
      (∀ x z, z ∈ mulLat (cBof t.sel (t.tup μ) (t.cst μ) (t.word u)) (homAt (Sall t.sel (t.tup μ) (t.word u)) N N') → f (x + z) = f x) →
      (∀ x, f (γ.1.toLinearMap ∘ₗ x) * ∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E) = k * f x) →
      TermLaw (t.O u μ) i c c' (matE t.seam γ.1, t.seam.σ₀ k) := by
    intro f N N' γ k hN1 hN2 hf hγ hinv hlaw
    subst hN1 hN2
    refine dat γ k hγ (fun x z hz => ?_) fun x => ?_
    · rw [hlev, hSS] at hz
      rw [hf, hf, hinv x z (mulLat_mul_le _ _ _ hz)]
    · rw [hf, hf, ← map_mul, ← map_mul, hlaw]
  rcases lt_trichotomy i t.m2 with hlt | heq | hgt
  · rw [hGi (i + 1) (by omega) (by omega) c'] at hg
    obtain ⟨a, hfix, -, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN i (by omega) c) (hN (i + 1) (by omega) c') (hE i hlt c c') (gmap_of_fix a _ hfix)
      (fun x z hz => xiEntry_invA t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.pr_ok hok i hlt _ _ _ _ x z hz)
      (GlobalTheory.FiLaw.xiEntry_stab t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (t.word u) i hlt _ _ _ _ a hfix)
  · subst heq
    obtain ⟨b, -⟩ := hok.last_uniq
    rw [hGm b c'] at hg
    obtain ⟨a, hfix, hY, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN _ (Nat.le_succ _) c) (hN _ le_rfl c') (hC1 c c') (gmap_of_fix a _ hfix)
      (fun x z hz => xiCpl1_invA t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.pr_ok hok _ _ _ _ x z hz)
      (GlobalTheory.StabLaw.xiCpl1_stab t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob _ hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (t.word u) _ b _ _ _ a (hyb c') hfix hY)
  · have hi' : i = t.m2 + 1 := by omega
    subst hi'
    rw [hGT c'] at hg
    obtain ⟨a, hfix, -, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN _ le_rfl c) (hTop.1 c') (hTop.2 c c') (gmap_of_fix a _ hfix)
      (fun x z hz => GlobalTheory.T.lastStep_datum_invariant_cB_hom_twist_primes t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok
        (t.word u) _ _ _ x z (hyb c) hz)
      (GlobalTheory.T.lastStepDatum_law_topLevelStabilizer t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (hC.deep μ).2 (t.word u) _ _ _ a (hyb c) hfix)

end GlobalTheory.KerJ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassSumTermLawStabiliserTargetStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.KerJ Classical

theorem _root_.GlobalTheory.T.classSum_term_law_stabiliser_target : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → ∀ u μ (G : StabDat (D.chTw u μ)), StabPin t u μ G → ∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw (t.O u μ) i c c' g := by
  first | exact @GlobalTheory.KerJ.term_law | exact GlobalTheory.KerJ.term_law | (intros; apply GlobalTheory.KerJ.term_law <;> assumption)
end
end
