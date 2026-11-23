module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterLocalUnitaryGroupFinitePlaceScalarStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.QuotientMetricDivisors.Statement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMulVec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntOfSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairLattice
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SdYFrames
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SdYFrames

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairTranslate

section

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.CentralUnitGen

theorem scalar_keeps {R : Type} [CommRing R] {S : Subring R} {n : ℕ} (Λ : Submodule S (Fin n → R)) (w : Fin n → R)
    (Mt Mt' Mk Mki : Matrix (Fin n) (Fin n) R) (c c' : R)
    (h1 : Mt = (c • (1 : Matrix (Fin n) (Fin n) R)) * Mt' * Mk) (h2 : (c' * c) • (1 : Matrix (Fin n) (Fin n) R) = 1)
    (hkk : Mk * Mki = 1)
    (hk : ∀ y, y ∈ Λ ↔ Matrix.mulVec Mk y ∈ Λ) (hki : ∀ y, y ∈ Λ ↔ Matrix.mulVec Mki y ∈ Λ)
    (hw : ∀ c0 : R, ((∃ x ∈ Λ, Matrix.mulVec Mt x = c0 • w) ↔ c0 ∈ S) ∧ ((∃ x ∈ Λ, Matrix.mulVec Mt' x = c0 • w) ↔ c0 ∈ S)) :
    ∀ y, y ∈ Λ ↔ Matrix.mulVec (c • (1 : Matrix (Fin n) (Fin n) R)) y ∈ Λ := by
  have e2 : Mt' * Mk = (c' • (1 : Matrix (Fin n) (Fin n) R)) * Mt := by
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.smul_mul, Matrix.one_mul, smul_smul, h2, Matrix.one_mul]
  have hcI : c ∈ S := by
    obtain ⟨x', hx', ex'⟩ := ((hw 1).2).2 (one_mem _)
    refine ((hw c).1).1 ⟨Matrix.mulVec Mki x', (hki x').1 hx', ?_⟩
    rw [Matrix.mulVec_mulVec, h1, Matrix.mul_assoc, Matrix.mul_assoc, hkk, Matrix.mul_one, ← Matrix.mulVec_mulVec, ex', one_smul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hc'I : c' ∈ S := by
    obtain ⟨x, hx, ex⟩ := ((hw 1).1).2 (one_mem _)
    refine ((hw c').2).1 ⟨Matrix.mulVec Mk x, (hk x).1 hx, ?_⟩
    rw [Matrix.mulVec_mulVec, e2, ← Matrix.mulVec_mulVec, ex, one_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
  intro y
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · intro hy
    exact Λ.smul_mem ⟨c, hcI⟩ hy
  · intro hy
    have h3 := Λ.smul_mem ⟨c', hc'I⟩ hy
    have e3 : (c' * c) • y = y := by
      have := congrArg (fun A => Matrix.mulVec A y) h2
      simpa only [Matrix.smul_mulVec, Matrix.one_mulVec] using this
    rw [← e3, mul_smul]
    exact h3

end GlobalTheory.CentralUnitGen

namespace GlobalTheory.CentralUnitGen

theorem proj_mem_center {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {g : GlobalTheory.AdelicU.GAd σ J}
    (hg : g ∈ Subgroup.center (GlobalTheory.AdelicU.GAd σ J)) : GlobalTheory.AdelicU.proj σ J v g ∈ Subgroup.center (GlobalTheory.AdelicU.GLoc σ J v) := by
  refine Subgroup.mem_center_iff.2 fun x => ?_
  have e := congrArg (GlobalTheory.AdelicU.proj σ J v) (Subgroup.mem_center_iff.1 hg (GlobalTheory.AdelicU.emb σ J v x))
  rwa [map_mul, map_mul, GlobalTheory.AdelicU.proj_emb_self] at e

end GlobalTheory.CentralUnitGen

namespace GlobalTheory.MiTop


end GlobalTheory.MiTop

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CommonLine

section

@[expose] public section



section
noncomputable section


namespace GlobalTheory.LineIdeal
section Loc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc NumberField GlobalTheory.AdelicU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
end Loc
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix GlobalTheory.GoodPos
section Word
variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ}
end Word
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem single_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) (r : Fin D.R.rS) (hr : r.1 = 0) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (hP : _root_.GlobalTheory.MiTop.PlacedConditions f B) (a₀ a₁ : GA D (D.sp.X 0)) (x : GlobalTheory.FinPl.Pl D)
    (hg : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ x) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ x.asIdeal) {α cc : (AE D)ˣ}
    (hα : ∀ (S : Formalism.BasicNotions.TH.HSp D) (L : GlobalTheory.FinPl.Lat S) y,
      y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE W.Q.Rl.ψ (s * o) = 1) ↔
      ((cc⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x), mt (D.sp.Y 0) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a₁)⁻¹ *ᵥ (a •
      (((cc ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) : (AE D)ˣ) : AE D) *
        incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) •
      ratV fun k => W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) k))) ∈ latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = x) ↔
      a ∈ intAt D (· = x) := by
  intro a ha
  obtain ⟨k, i1, i2, i3, i4, ι, v, o, n, G, pl, hc, -, ht, sh, -, -, hb, hp⟩ := hP
  obtain ⟨μ, lam, n1, n2, n3⟩ := hb.norm
  have hξ : -D.host.xi0 ^ (D.R.m / 2) ≠ 0 := neg_ne_zero.2 (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (n1 ▸ hξ)
  have hlam : lam ≠ 0 := right_ne_zero_of_mul (n1 ▸ hξ)
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.rS
    omega
  obtain ⟨s, hs, he⟩ := first_vec (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) hW.bot.idE hc.std B hμ n2 r hr
  have hI := all_ideal hc sh (fun n h x hx => by subst h; exact hp x hx) (fun j hj => by
      change 0 < (D.sp.X (j + 1)).rank
      rw [Formalism.L2.Forms.rankN D _ hj]
      unfold Ranks.N
      have := D.R.m_add_three_le_k
      omega) hlam n3 (fun e => hx ((ht.tP x).1 e)) hα hψ 0 D.R.rS h₀ (D.R.rS - 1) r (by have := r.2; omega)
  have hd : B.d.e = (f.c.bes 0 D.R.rS h₀).d.e := eq_of_heq (Sigma.mk.inj (congrArg
    (fun Z : BesLev D D.R.rS => (⟨Z.V.rank, Z.d.e⟩ : Σ n, Matrix (Fin n) (Fin D.R.rS) D.host.E)) (hb.lev h₀))).2
  have hm := ht.moves 0 (by omega) (· = x) fun p hp e => by
    obtain ⟨PP, h1, h2⟩ := (ht.gP p).1 e
    exact hg PP h1 (h2.symm.trans hp)
  have hx1 := xu_fixes (h := W.Q.instEq) (u := u) hW.bot.idE r
  rw [← mul_assoc (α * α), ← mul_assoc (cc ^ _)] at hI
  generalize cc ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) = K at hI ⊢
  obtain ⟨ε, hε⟩ : ∃ ε : Fin (D.sp.Y 0).rank → D.host.E,
      (fun k => W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) k))) = ε := ⟨_, rfl⟩
  have he' : ∀ k, B.d.e k r = s * (μ * (W.S.X.B.g : D.host.E) ^ D.R.rS) * ε k := fun k => by rw [he, ← hε]
  rw [hε] at hx1 ⊢
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> simp
  have hy : a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε =
      colMul B.d.jX r ((K : AE D) * incA D lam * (incA D (-s) * a)) := by
    funext k
    change a * (_ * incA D (ε k)) = _ * incA D (B.d.e k r)
    have : D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS * ε k = lam * -s * B.d.e k r := by
      rw [he']
      linear_combination ((W.S.X.B.g : D.host.E) ^ D.R.rS * ε k) * n1 + (lam * μ * (W.S.X.B.g : D.host.E) ^ D.R.rS * ε k) * hss
    have h2 := congrArg (incA D) this
    rw [map_mul, map_mul (incA D) (lam * -s), map_mul (incA D) lam] at h2
    linear_combination (a * K) * h2
  have hfix : mt (D.sp.Y 0) ((show GA D (D.sp.Y 0) from f.g.b 0) * (_root_.GlobalTheory.MiTop.translationElement f B a₀ a₁)⁻¹) *ᵥ
      (a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε) =
      colMul B.d.jX r ((K : AE D) * incA D lam * (incA D (-s) * a)) := by
    have e : (show GA D (D.sp.Y 0) from f.g.b 0) * (_root_.GlobalTheory.MiTop.translationElement f B a₀ a₁)⁻¹ =
        embA B.d B.o (a₀ * a₁)⁻¹ * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      unfold _root_.GlobalTheory.MiTop.translationElement
      rw [map_inv, _root_.mul_inv_rev, mul_inv_cancel_left, _root_.mul_inv_rev, inv_inv]
    rw [e, GlobalTheory.MixModel.mt_mul, ← mulVec_mulVec, mulVec_smul (mt _ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))), mulVec_smul (mt _ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))), hx1, hy]
    generalize (K : AE D) * incA D lam * (incA D (-s) * a) = t
    have e1 : colMul B.d.jX r t = B.d.jX *ᵥ Pi.single r t := by
      rw [mulVec_single]; funext k; exact mul_comm _ _
    rw [e1, mulVec_mulVec, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX]
  have hsup : ∀ i, (a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε) i ∈
      idAt D (· = x) := fun i => Ideal.mul_mem_right _ _ ha
  rw [GlobalTheory.MixModel.mt_mul, ← mulVec_mulVec] at hfix
  have hj : B.d.jX = (f.c.bes 0 D.R.rS h₀).d.jX := congrArg rat hd
  have h1 := hI ((K : AE D) * incA D lam * (incA D (-s) * a)) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha))
  rw [← inU_val lam hlam, ← Units.val_mul, Units.inv_mul_cancel_left, Units.val_mul, inU_val, ← hj] at h1
  refine (hm _ (GlobalTheory.FinPl.KOpen.supp_mulVec (D.sp.Y 0) _ _ hsup)).trans
    ((iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v.N 0) (· = x)) hfix)).trans (h1.trans ?_))
  rcases hs with rfl | rfl
  · rw [map_neg, map_one, neg_one_mul, int_neg]
  · rw [neg_neg, map_one, one_mul]
theorem common_line_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∃ w : Fin (D.sp.Y 0).rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ((∃ x ∈ GlobalTheory.AdelicU.latLoc D.host.F ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v, Matrix.mulVec (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (_root_.GlobalTheory.MiTop.translationElement f B a₀ a))).1 x = c • w) ↔ c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) ∧ ((∃ x ∈ GlobalTheory.AdelicU.latLoc D.host.F ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v, Matrix.mulVec (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a'))).1 x = c • w) ↔ c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' _ _ v hg hu hu'
  have hstd : IsStdChar D W.Q.Rl.ψ (-1) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, -⟩ := hP
    exact hc.std
  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D _ hstd
  have hψ : ∀ s ∈ idAt D (· = v), (∀ o ∈ intAt D (· = v), psiE W.Q.Rl.ψ (s * o) = 1) ↔
      (((xiU D * α * cU α)⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = v) := fun s hs => by
    rw [(hα v).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  have hfg : ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0).FG := (_root_.GlobalTheory.Fam.sdY_frames_alt W hW 0 (by have := D.R.two_le_m; omega)).1.1.fg
  exact ⟨_, fun c => ⟨line_loc (D.sp.Y 0) _ hfg v _ _ (_root_.GlobalTheory.LineIdeal.single_alt W hW ⟨0, hr⟩ rfl f B hP a₀ a v hg hu (hα v).1 hψ) c,
    line_loc (D.sp.Y 0) _ hfg v _ _ (_root_.GlobalTheory.LineIdeal.single_alt W hW ⟨0, hr⟩ rfl f' B' hP' a₀' a' v hg hu' (hα v).1 hψ) c⟩⟩
end GlobalTheory.LineIdeal
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CommonLineStatement

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.placed_bessel_pair_lattice_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∃ w : Fin (D.sp.Y 0).rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ((∃ x ∈ GlobalTheory.AdelicU.latLoc D.host.F ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v, Matrix.mulVec (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (_root_.GlobalTheory.MiTop.translationElement f B a₀ a))).1 x = c • w) ↔ c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) ∧ ((∃ x ∈ GlobalTheory.AdelicU.latLoc D.host.F ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v, Matrix.mulVec (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a'))).1 x = c • w) ↔ c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) := by
  first | exact @_root_.GlobalTheory.LineIdeal.common_line_alt | exact _root_.GlobalTheory.LineIdeal.common_line_alt | (intros; apply _root_.GlobalTheory.LineIdeal.common_line_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralRatioUnitGen

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.CentralUnitGen
end GlobalTheory.CentralUnitGen
namespace GlobalTheory.CentralUnitGen
end GlobalTheory.CentralUnitGen
namespace GlobalTheory.MiTop


theorem centralRatio_unit_gen_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr u u' f f' B B' hPl hPl' a₀ a a₀' a' hA hA' z hzf hzc k hk he v hv hTu hTu'
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hfr := (_root_.GlobalTheory.Fam.sdY_frames_alt W hP 0 hm).2
  have hkS : Formalism.IndefR.Lev.finE (Yc D 0) k ∈ Formalism.L2.DIV.St ((_root_.GlobalTheory.Fam.pk_z W).βY 0) :=
    Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk.2)
  have hkv := (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (Yc D 0) _ ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) hfr k).1 hkS v
  have hkv' := Subgroup.inv_mem _ hkv
  obtain ⟨c, hc⟩ := GlobalTheory.T.center_localUnitaryGroup_finitePlace_scalar D (D.sp.Y 0) v _ (GlobalTheory.CentralUnitGen.proj_mem_center _ _ v hzc)
  obtain ⟨c', hc'⟩ := GlobalTheory.T.center_localUnitaryGroup_finitePlace_scalar D (D.sp.Y 0) v _ (GlobalTheory.CentralUnitGen.proj_mem_center _ _ v (Subgroup.inv_mem _ hzc))
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.T.placed_bessel_pair_lattice_alt W hP hr u u' f f' B B' hPl hPl' a₀ a a₀' a' hA hA' v hv hTu hTu'
  have h2 : (c' * c) • (1 : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) = 1 := by
    have h := congrArg (fun g => (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v g)).1) (inv_mul_cancel z)
    simp only [map_mul, map_one, Units.val_mul, Units.val_one] at h
    rw [hc, hc', Matrix.smul_mul, Matrix.one_mul, smul_smul] at h
    exact h
  have h1 := congrArg (fun g => (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v g)).1) he
  simp only [map_mul, Units.val_mul] at h1
  rw [hc] at h1
  have hkk : (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v k)).1 *
      (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v k)⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  refine GlobalTheory.AdelicU.mem_stabLoc.2 ?_
  rw [hc]
  exact GlobalTheory.CentralUnitGen.scalar_keeps _ w _ _ _ _ c c' h1 h2 hkk (GlobalTheory.AdelicU.mem_stabLoc.1 hkv)
    (GlobalTheory.AdelicU.mem_stabLoc.1 hkv') hw
end GlobalTheory.MiTop
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralRatioUnitGenStatement

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.placed_bessel_pair_translate_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v := by
  first | exact @_root_.GlobalTheory.MiTop.centralRatio_unit_gen_alt | exact _root_.GlobalTheory.MiTop.centralRatio_unit_gen_alt | (intros; apply _root_.GlobalTheory.MiTop.centralRatio_unit_gen_alt <;> assumption)
end
end
end
