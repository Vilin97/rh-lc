module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeActionFramedPointsOfUnipotentModTwoPrimes
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCongruenceSelfDualOfPrincipalLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinalRowGramAlgebraicSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameReductionEqOneOfCongruentModIdealStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveLiftCongruentModIdealStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinalRowWeightGramAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemLatGHat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeActionFramedPointsOfUnipotentModTwoPrimesStatement

section

@[expose] public section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.free_action_framedPoints_of_unipotent_mod_two_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (G : Type) [Group G] (h : G → (Dw.La →ₗ[𝓞 E] Dw.La)) (m g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)), 1 ≤ Dw.p + Dw.q → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → l.Mb ≤ I₁ → l.Mb ≤ I₂ → (∀ g x, ((h g - 1) ^ m) x ∈ I₁ • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ g x, ((h g - 1) ^ m) x ∈ I₂ • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ g, (∀ x, h g x - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → g = 1) → FreePt Xo c (fun g => (h g, (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La))) := by
  first | exact @GlobalTheory.FreeLev.free_of_unip | exact GlobalTheory.FreeLev.free_of_unip | (intros; apply GlobalTheory.FreeLev.free_of_unip <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointFieldAlgebraicallyClosed

section

@[expose] public section


open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree

theorem mem_smul_top_of_coprime {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] (I J : Ideal R) (hIJ : J ⊔ I = ⊤)
    (f : N →ₗ[R] N) (h : ∀ z ∈ J • (⊤ : Submodule R N), f z ∈ I • (⊤ : Submodule R N)) (x : N) :
    f x ∈ I • (⊤ : Submodule R N) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hIJ ▸ Submodule.mem_top : (1 : R) ∈ J ⊔ I)
  have e : f x = f (a • x) + b • f x := by rw [map_smul, ← add_smul, hab, one_smul]
  rw [e]
  exact add_mem (h _ (Submodule.smul_mem_smul ha Submodule.mem_top)) (Submodule.smul_mem_smul hb Submodule.mem_top)

theorem natCast_not_isUnit {K : Type} [Field K] [NumberField K] {g : ℕ} (hg : g.Prime) : ¬ IsUnit (g : 𝓞 K) := by
  intro hu
  have h1 := hu.map (Algebra.norm ℤ : 𝓞 K →* ℤ)
  have e : ((g : 𝓞 K)) = algebraMap ℤ (𝓞 K) (g : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap] at h1
  have hn : Module.finrank ℤ (𝓞 K) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hn, Int.isUnit_iff] at h1
  have := hg.two_le
  rcases h1 with h1 | h1 <;> omega

theorem sup_span_ne_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H)
    {g : ℕ} (hg : g.Prime) (hd : g ∣ l.M) : l.Mb ⊔ Ideal.span {(g : 𝓞 E)} ≠ ⊤ := by
  intro htop
  have hb : Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb ⊔ Ideal.span {(g : 𝓞 E)} = ⊤ := by
    have := congrArg (Ideal.map (H.bar : 𝓞 E →+* 𝓞 E)) htop
    rwa [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_top] at this
  have hle : (⊤ : Ideal (𝓞 E)) ≤ Ideal.span {(g : 𝓞 E)} := by
    calc (⊤ : Ideal (𝓞 E)) = (l.Mb ⊔ Ideal.span {(g : 𝓞 E)}) * (Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb ⊔ Ideal.span {(g : 𝓞 E)}) := by
          rw [htop, hb, Ideal.top_mul]
      _ ≤ Ideal.span {(g : 𝓞 E)} := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, l.prod]
          refine sup_le (sup_le ?_ (Ideal.mul_le_inf.trans inf_le_right)) (sup_le (Ideal.mul_le_inf.trans inf_le_left) (Ideal.mul_le_inf.trans inf_le_left))
          rw [Ideal.span_singleton_le_span_singleton]
          exact_mod_cast (Nat.cast_dvd_cast hd : ((g : 𝓞 E)) ∣ (l.M : 𝓞 E))
  exact natCast_not_isUnit hg (Ideal.span_singleton_eq_top.1 (top_le_iff.1 hle))

end GlobalTheory.DefFree
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EqOneOfLevCong

section

@[expose] public section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseLevelInj
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR
end GlobalTheory.BaseLevelInj

open GlobalTheory.BaseLevelInj in
theorem GlobalTheory.BaseLevelInj.eq_one_of_lev_sub_mem_Mb : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ g : (p.F.lv2.lvl false).P, (∀ x : (p.T.Q.Dw ((i : ℕ) + 1)).La, (p.O i).lev (g : p.P.Gp) x - x ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) → g = 1 := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF g hg
  obtain ⟨κ, hlift, happ⟩ := (p.pins i).2.lift.lev (g : p.P.Gp)
  have hβ := p.charW.base.lev.βW i
  have hSt := Formalism.L2.DIV.parLev_St hlift.2.1
  have hfc := GlobalTheory.LevelAction.finCong_of_mem_St hβ hSt
  have hι := GlobalTheory.LevelAction.latEmb_iotaW p.T p.fw.laws i
  have hMb : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb := by
    have h0 : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := Ideal.mem_span_singleton_self _
    rw [← p.T.Q.l.prod] at h0
    exact (Ideal.mul_le_inf.trans inf_le_left : p.T.Q.l.Mb * _ ≤ p.T.Q.l.Mb) h0
  have h4 := GlobalTheory.T.levelMove_lift_congruent_mod_ideal (Wc D i) (iotaW p.T i) hι p.T.Q.l.M p.T.Q.l.Mb (Mfr p.T.Q.l) p.T.Q.l.coprime hMb κ hfc
    ((p.O i).lev (g : p.P.Gp)) happ hg
  have h3 := GlobalTheory.T.adelicCongruence_selfDual_of_principalLattice (Wc D i) _ _ h4
  rw [← GlobalTheory.PrincInLevel.eq_latC hβ] at h3
  have h2 := hatL_cong_of_hat (Wc D i) κ _ _ h3
  have hfr : Formalism.L2.DIV.IsFrame (p.R.βW i) (p.R.ΛW i) := by obtain ⟨c, h, -⟩ := hβ; exact h
  have hhalf := ((p.pins i).2.tuple ()).half.1
  have hred : ∀ PP ∈ p.R.Pg, Formalism.L2.DIV.redFn (p.R.βW i) PP (Formalism.IndefR.Lev.finE (Wc D i) κ) = 1 := by
    intro PP hP
    refine GlobalTheory.T.frameReduction_eq_one_of_congruent_mod_ideal _ _ _ hfr hSt _ h2 PP ?_
    rw [hhalf]
    exact Ideal.prod_le_inf.trans (Finset.inf_le hP)
  have hT1 : Formalism.L2.DIV.rTup (p.R.βW i) (p.R.datWp i p.R.triv) (Formalism.IndefR.Lev.finE (Wc D i) κ) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn (p.R.βW i) PP.1 _) = 1
    rw [hred PP.1 PP.2]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  have he : p.R.eG (g : p.P.Gp) = 1 := by rw [← hlift.2.2]; exact hT1
  have : (g : p.P.Gp) = 1 := by rw [← map_one p.R.eG] at he; exact p.R.eG.injective he
  exact Subtype.ext this
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EqOneOfLevCongStatement

section

@[expose] public section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eq_one_of_lev_sub_mem_Mb_gram : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ g : (p.F.lv2.lvl false).P, (∀ x : (p.T.Q.Dw ((i : ℕ) + 1)).La, (p.O i).lev (g : p.P.Gp) x - x ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) → g = 1 := by
  first | exact @_root_.GlobalTheory.BaseLevelInj.eq_one_of_lev_sub_mem_Mb | exact _root_.GlobalTheory.BaseLevelInj.eq_one_of_lev_sub_mem_Mb | (intros; apply _root_.GlobalTheory.BaseLevelInj.eq_one_of_lev_sub_mem_Mb <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnipModHalf

section

@[expose] public section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.LevelUnip
section Res
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
end Res
variable {D : D7}
end GlobalTheory.LevelUnip
open GlobalTheory.LevelUnip in
theorem GlobalTheory.LevelUnip.unip_mod_half_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ (g : (p.F.lv2.lvl false).P) (z : (p.T.Q.Dw ((i : ℕ) + 1)).La), z ∈ Mfr p.T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) → (((p.O i).lev (g : p.P.Gp) - 1) ^ D.R.r) z ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF g z hz
  obtain ⟨κ, hk, hf⟩ := (p.pins i).2.lift.lev g
  have hB := p.charW.base
  obtain ⟨ψ0, -, hlev, -⟩ := hB.grp.levels
  have hL := hB.lev
  have hu : p.R.eG g ∈ (p.R.levR p.F.lv2 false).H := by
    show p.R.eG.symm.toMonoidHom (p.R.eG g) ∈ (p.F.lv2.lvl false).P
    simp
  have hun : ∀ PP, p.R.eG g PP ∈ unip (kP PP.1) D.R.r := by
    rw [hlev] at hu
    exact fun PP => (Subgroup.mem_pi _).1 hu PP (Set.mem_univ _)
  have hhalf := ((p.pins i).2.tuple ()).half.1
  have hemb := GlobalTheory.LevelAction.latEmb_iotaW p.T p.fw.laws i
  have hβ := hL.βW i
  have hr := rank_Wc (D := D) i
  have hkSt := parLev_St hk.2.1
  have hred : ∀ P ∈ p.R.Pg, (((redFn (p.R.βW i) P (Lev.finE (Wc D i) κ) : GL (Fin (Wc D i).rank) (kP P)) :
      Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP P)) - 1) ^ D.R.r = 0 := by
    intro P hP
    have hb := blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP)
    have e : upperLeftBlock (p.R.datWp i p.R.triv).hr (redFn (p.R.βW i) P (Lev.finE (Wc D i) κ)) = p.R.eG g ⟨P, hP⟩ :=
      congrFun hk.2.2 ⟨P, hP⟩
    have hU := hun ⟨P, hP⟩
    rw [← e] at hU
    have hv := upper_block_val_submatrix (p.R.datWp i p.R.triv).hr hb
    have hent : ∀ a c : Fin (Wc D i).rank,
        ((upperLeftBlock (p.R.datWp i p.R.triv).hr (redFn (p.R.βW i) P (Lev.finE (Wc D i) κ)) : GL (Fin D.R.r) (kP P)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (kP P)) (Fin.cast hr a) (Fin.cast hr c) =
        ((redFn (p.R.βW i) P (Lev.finE (Wc D i) κ) : GL (Fin (Wc D i).rank) (kP P)) :
          Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP P)) a c := by
      intro a c
      exact (congrFun (congrFun hv (Fin.cast hr a)) (Fin.cast hr c)).trans rfl
    rw [← hr]
    apply sub_one_pow_eq_zero'
    · intro a c hca
      rw [← hent]
      exact hU.1 (show ((Fin.cast hr c : Fin D.R.r) : ℕ) < (Fin.cast hr a : Fin D.R.r) from hca)
    · intro a
      rw [← hent]
      exact hU.2 _
  have hp : p.T.Q.l.Mb * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := p.T.Q.l.prod
  have hp' : (∏ P ∈ p.R.Pg, P.asIdeal) * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := by
    rw [← hhalf]; exact hp
  have hI : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb :=
    (hp.ge.trans (Ideal.mul_le_inf.trans inf_le_left)) (Ideal.mem_span_singleton_self _)
  have hc : p.T.Q.l.Mb ⊔ Mfr p.T.Q.l = ⊤ := p.T.Q.l.coprime
  have hcong := fun b (hb : b ∈ Mfr p.T.Q.l) => exists_pow_cong hβ p.R.Pg hp' hkSt hred hb
  have hpow := approx_pow hemb (sub_one_mulVec_mem hβ hkSt) hf D.R.r
  have h0 : ∀ a ∈ Mfr p.T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La),
      ∃ w ∈ latGHat (Wc D i) 1, finVec (Wc D i) (iotaW p.T i ((0 : (p.T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] _) a)) -
        (0 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ
          finVec (Wc D i) (iotaW p.T i a) = p.T.Q.l.M • w := by
    intro a _
    refine ⟨0, zero_mem _, ?_⟩
    funext j
    simp [finVec]
  have := GlobalTheory.LevelUnique.sub_mem_of_approx hemb (lt_of_lt_of_le (by norm_num) p.T.Q.l.three_le) hI hc hcong hpow h0 z
  simpa using this
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnipModHalfStatement

section

@[expose] public section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lev_sub_one_pow_mem_level_multiple : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ (g : (p.F.lv2.lvl false).P) (z : (p.T.Q.Dw ((i : ℕ) + 1)).La), z ∈ Mfr p.T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) → (((p.O i).lev (g : p.P.Gp) - 1) ^ D.R.r) z ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
  first | exact @_root_.GlobalTheory.LevelUnip.unip_mod_half_alt | exact _root_.GlobalTheory.LevelUnip.unip_mod_half_alt | (intros; apply _root_.GlobalTheory.LevelUnip.unip_mod_half_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FreeBase

section

@[expose] public section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefFree
theorem free_base_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := p.fw.laws.pins.2.1.1
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, by omega⟩
  have hpq : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).p + (p.T.Q.Dw ((i : ℕ) + 1)).q := by
    have h1 := (p.fw.laws.pins.2.2.2 _ hj).1
    have h2 := D.R.m_add_three_le_k
    rw [h1]
    simp only [Ranks.sigW]
    omega
  have hun : ∀ (g : (p.F.lv2.lvl false).P) (x : (p.T.Q.Dw ((i : ℕ) + 1)).La),
      (((p.O i).lev (g : p.P.Gp) - 1) ^ D.R.r) x ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) :=
    fun g x => mem_smul_top_of_coprime _ _ (by rw [sup_comm]; exact p.T.Q.l.coprime) _
      (_root_.GlobalTheory.T.lev_sub_one_pow_mem_level_multiple p i PP A M hR hi hG hW hH hF g) x
  exact GlobalTheory.T.free_action_framedPoints_of_unipotent_mod_two_primes D.host.E p.T.Q.H (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
    (p.F.lv2.lvl false).P (fun g => (p.O i).lev (g : p.P.Gp)) D.R.r (D.host.g 0) (D.host.g 1)
    (p.T.Q.l.Mb ⊔ Ideal.span {((D.host.g 0 : ℕ) : 𝓞 D.host.E)}) (p.T.Q.l.Mb ⊔ Ideal.span {((D.host.g 1 : ℕ) : 𝓞 D.host.E)})
    hpq (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
    (sup_span_ne_top _ (D.host.g_prime 0) (by rw [hM]; exact dvd_mul_right _ _))
    (sup_span_ne_top _ (D.host.g_prime 1) (by rw [hM]; exact dvd_mul_left _ _))
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    le_sup_left le_sup_left (fun g x => Submodule.smul_mono_left le_sup_left (hun g x))
    (fun g x => Submodule.smul_mono_left le_sup_left (hun g x)) (_root_.GlobalTheory.T.eq_one_of_lev_sub_mem_Mb_gram p i PP A M hR hi hG hW hH hF)
end GlobalTheory.DefFree
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FreeBaseStatement

section

@[expose] public section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.freePt_last_index_of_fnAlgClosed : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) := by
  first | exact @_root_.GlobalTheory.DefFree.free_base_alt | exact _root_.GlobalTheory.DefFree.free_base_alt | (intros; apply _root_.GlobalTheory.DefFree.free_base_alt <;> assumption)
end
end
end
