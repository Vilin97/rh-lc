module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsContAutRTrans
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TprodEqZeroOfKFinOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitGramAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultRealElt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientDecayKFiniteSecondVectorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesMoveRealPointStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBoundMultiplicityValueExceedsHalfStatement
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormCuspFormLeOfShortLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesIdentityTermDominates
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRowGridBottomSelfDualLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentPeriodAdelicClausesOfReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentPeriodValueLipschitzRealOneParameterStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ExistsMultTEqPoin
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCuspFormPeriodNeZero

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer.PerNe

theorem multT_apply_mul_lev {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S}
    {J : Set (GA D V)} {χ : GA D V → ℂ} {F : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    ∀ k ∈ J, ∀ g, F v (g * k) = χ k * F v g := by
  obtain ⟨T, hT, rfl⟩ := hF
  induction hT using Submodule.span_induction generalizing v with
  | mem T hT =>
    induction v using PiTensorProduct.induction_on with
    | smul_tprod r w =>
      intro k hk g
      simp only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul]
      rw [hT.lev w k hk g]; ring
    | add x y hx hy =>
      intro k hk g
      simp only [map_add (f := _), Pi.add_apply]
      rw [hx k hk g, hy k hk g]; ring
  | zero => intro k hk g; simp
  | add T₁ T₂ _ _ h₁ h₂ =>
    intro k hk g
    simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
    rw [h₁ v k hk g, h₂ v k hk g]; ring
  | smul c T _ h =>
    intro k hk g
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [h v k hk g]; ring

theorem apply_tprod_eq {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    {X : Type} [AddCommGroup X] [Module ℂ X] (y : (⨂[ℂ] i, E i) →ₗ[ℂ] X) (a : ∀ i, E i) :
    y (PiTensorProduct.tprod ℂ a) = PiTensorProduct.lift.symm y a := by
  conv_lhs => rw [← PiTensorProduct.lift.apply_symm_apply y]
  exact PiTensorProduct.lift.tprod _

end GlobalTheory.SepPer.PerNe

namespace GlobalTheory.SepPer

end GlobalTheory.SepPer

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormCuspFormLeOfShortLineStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_cuspForm_le_of_shortLine : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∀ (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ V.rank → (∀ τ, min (Finset.univ.filter fun a => A.ε τ a = true).card (Finset.univ.filter fun a => A.ε τ a = false).card ≤ q) → ∀ φ : GA D V → ℂ, IsAutFun V φ → IsCuspFun V φ → (∀ k ∈ Lev.levA V (congLev D.sp.cm V.gram Λ (Ideal.span {((g : ℕ) : 𝓞 D.host.E)})), ∀ x, φ (x * k) = φ x) → ∀ c : ℝ, 0 ≤ c → Lip θ A φ c → ∀ (x : GA D V) (s : ℝ), 0 < s → s ≤ 1 / 2 → ¬ Long θ A Λ x s → ‖φ x‖ ≤ c * ((V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D * (2 * s) ^ ((1 : ℝ) / q)) := by
  first | exact @GlobalTheory.ShortLineCusp.norm_le_of_not_long | exact GlobalTheory.ShortLineCusp.norm_le_of_not_long | (intros; apply GlobalTheory.ShortLineCusp.norm_le_of_not_long <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesIdentityTermDominatesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.poincareSeries_pairing_ne_zero_of_large_level : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S') (M : DSModel V S) (p : Pack M₀ M) (Q : ℝ), p.Base d → ∀ (Λ : Lat Y) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC Y Λ → 𝔪 ≠ ⊥ → ∀ (v : GlobalTheory.Unf.Vol Y) (φ : GA D Y → ℂ) (c : ℂ) (b s : ℝ) (x : GA D Y), GlobalTheory.Unf.IsContAut Y φ → (∀ h, ‖φ h‖ ≤ b) → b / 2 < ‖φ x‖ → 0 ≤ s → s ≤ 1 → Long θ p.A Λ x s → p.AdelicAt θ d Q (d.lat Λ fun _ => 1) 𝔪 v.μ φ c → 2 * Real.exp (Q + (6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau) ≤ s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) → 1 < s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) → ∫ h in v.𝓕, poin θ M (congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪) (p.v θ) (stabilizerEmbedding d x⁻¹) (p.v θ) (stabilizerEmbedding d h) * φ h ∂v.μ ≠ 0 := by
  first | exact @GlobalTheory.IdDom.identity_dominates | exact GlobalTheory.IdDom.identity_dominates | (intros; apply GlobalTheory.IdDom.identity_dominates <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentPeriodAdelicClausesOfRealStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotentPeriod_adelic_clauses_of_real : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S') (M : DSModel V S) (p : Pack M₀ M) (Q : ℝ), p.Is θ d Q → ∀ (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → zv d ∈ Λ → ∀ (J : Set (GA D Y)), (∀ k ∈ GfC Y, Lev.finE V (stabilizerEmbedding d k) ∈ congLev D.sp.cm V.gram Λ 𝔪 → k ∈ J) → ∀ t ∈ MultT θ M₀ J 1, ∀ ν : Measure (GA D Y), ν.IsHaarMeasure → ∃ c, p.AdelicAt θ d Q Λ 𝔪 ν (t (PiTensorProduct.tprod ℂ p.w)) c := by
  first | exact @GlobalTheory.SepPer.AdelicFromReal.adelicAt_of_real | exact GlobalTheory.SepPer.AdelicFromReal.adelicAt_of_real | (intros; apply GlobalTheory.SepPer.AdelicFromReal.adelicAt_of_real <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Period

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Cusp



open GlobalTheory.SepPer.PerNe in
theorem exists_cusp_form_theta_period_ne_zero : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    GlobalTheory.Published.CuspRapidDecay → PackEx → DepthPays →
    Ev fun {D} _ {L} {sc} {G} W M => ∀ (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0))
      (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))), ∀ t ∈ Rows L W.θ M₀, t ≠ 0 →
        ∃ y ∈ CoreForms G W.θ 0 MP, ∃ v w, per0 G M (y v) (t w) ≠ 0 := by
  intro hHC hCW hCRD hPE hDP
  obtain ⟨C, hC, hPack⟩ := hPE
  intro ε CF hCF
  obtain ⟨x₁, hx₁⟩ := hPack ε CF hCF
  obtain ⟨x₂, hx₂⟩ := hDP C hC ε CF hCF
  refine ⟨max x₁ x₂, ?_⟩
  intro D large₂ hε hx hSz T L μ0 hL G W M hM M₀ MP t ht ht0
  obtain ⟨p, hp⟩ := hx₁ D large₂ hε (le_trans (le_max_left _ _) hx) hSz T L μ0 hL G W M hM M₀ MP
  obtain ⟨s, hs0, hs1, hsLip, hsN1, hsN2⟩ := hx₂ D large₂ hε (le_trans (le_max_right _ _) hx) hSz T L μ0 hL G W M hM
  obtain ⟨hsdY, hsdV, hlam, hz0, hJ, hrY, hrV, hmY⟩ :=
    GlobalTheory.T.thetaRowGrid_bottom_selfDual_lattices D (offQ_of_sizeRows hSz) T L μ0 hL _ G W M hM

  have hθ : IsInfFam W.θ := W.θ_is
  have hmod : G.modul ≠ ⊥ := G.pl.modul_ne_bot _
  have hRow := (hM.row 0 (Nat.zero_le _)).haar_fund
  obtain ⟨v, hvμ, hv𝓕⟩ : ∃ v : GlobalTheory.Unf.Vol (Yc D 0), v.μ = M.ν (.grid 0 0) ∧ v.𝓕 = M.fd (.grid 0 0) :=
    ⟨⟨_, _, hRow.1, hRow.2⟩, rfl, rfl⟩
  obtain ⟨b, x, hb, hbx⟩ := GlobalTheory.T.exists_bound_multiplicity_value_exceeds_half hCRD D W.θ hθ (Yc D 0) (parB (Ptw D) 0) M₀ (levRow L : Set (GA D (Yc D 0))) v t ht ht0 p.w hp.1.ne
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb x)
  obtain ⟨hAutSm, hCusp, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hCRD D (Yc D 0) _ M₀ W.θ hθ _ 1 t ht
    (PiTensorProduct.tprod ℂ p.w)
  have hLip := GlobalTheory.T.unipotentPeriod_value_lipschitz_realOneParameter hCRD D W.θ hθ (Yc D 0) (G.V (.core 0)) G.sp.dec0 _ _ M₀ MP p (loss D C large₂.sc.b) hp (levRow L : Set (GA D (Yc D 0))) 1 t ht b hb
  have hInv : ∀ k ∈ Lev.levA (Yc D 0) (congLev D.sp.cm (Yc D 0).gram (L.ΛY 0)
      (Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)})), ∀ y, t (PiTensorProduct.tprod ℂ p.w) (y * k) = t (PiTensorProduct.tprod ℂ p.w) y := by
    intro k hk y
    rw [multT_apply_mul_lev ht _ k hk y, Pi.one_apply, one_mul]
  have hLong : Long W.θ p.A (L.ΛY 0) x s := by
    by_contra hn
    have hg1 : 1 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
    have hm1 : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    have hr1 : 1 ≤ (Yc D 0).rank := by rw [hrY]; exact (odd_r D).pos
    have hmin : ∀ τ, min (Finset.univ.filter fun a => p.A.ε τ a = true).card
        (Finset.univ.filter fun a => p.A.ε τ a = false).card ≤ D.R.m := fun τ => min_le_of_right_le (hmY p.A τ)
    have h := GlobalTheory.T.norm_cuspForm_le_of_shortLine D W.θ hθ (Yc D 0) p.A (L.ΛY 0) hsdY (D.host.g 0 * D.host.g 1) D.R.m hg1 hm1 hr1 hmin (t (PiTensorProduct.tprod ℂ p.w))
      hAutSm.toIsAutFun hCusp hInv (Real.exp (loss D C large₂.sc.b) * b) (by positivity) hLip x s hs0 hs1 hn
    rw [hrY] at h
    have : ‖t (PiTensorProduct.tprod ℂ p.w) x‖ ≤ b / 2 := by
      refine h.trans ?_
      have := mul_le_mul_of_nonneg_left hsLip hb0
      nlinarith
    linarith
  rw [hlam] at hsdV hz0
  have hJ' : ∀ k ∈ GfC (Yc D 0), Lev.finE (G.V (.core 0)) (stabilizerEmbedding G.sp.dec0 k) ∈
      congLev D.sp.cm (G.V (.core 0)).gram (G.sp.dec0.lat (L.ΛY 0) fun _ => 1) G.modul → k ∈ (levRow L : Set (GA D (Yc D 0))) := by
    rw [← hlam]; exact hJ
  obtain ⟨c, hc⟩ := GlobalTheory.T.unipotentPeriod_adelic_clauses_of_real hCRD D W.θ hθ (Yc D 0) (G.V (.core 0)) G.sp.dec0 _ _ M₀ MP p (loss D C large₂.sc.b) hp
    (G.sp.dec0.lat (L.ΛY 0) fun _ => 1) G.modul hsdV hmod hz0 (levRow L : Set (GA D (Yc D 0))) hJ' t ht v.μ v.haar
  have hN1 : 2 * Real.exp (loss D C large₂.sc.b + (6 * ((G.V (.core 0)).rank : ℝ) + 9) * Fintype.card D.what₂.Tau) ≤
      s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm G.modul) := by
    rw [hrV]; push_cast; exact hsN1
  have hne := GlobalTheory.T.poincareSeries_pairing_ne_zero_of_large_level D W.θ hθ (Yc D 0) (G.V (.core 0)) G.sp.dec0 _ _ M₀ MP p (loss D C large₂.sc.b) hp.1 (L.ΛY 0) G.modul hsdY hmod v (t (PiTensorProduct.tprod ℂ p.w)) c b s
    x (GlobalTheory.Core.Mi.BotPin.isContAut_multT ht _) hb hbx hs0.le (by linarith) hLong hc hN1 hsN2
  have hKD : KDecay MP p.v₀ := fun τ => ⟨(hp.1.dec τ).1, fun a ha =>
    GlobalTheory.T.coefficientDecay_kFinite_second_vector hHC D _ _ MP τ (p.v₀ τ) _ (hp.1.dec τ).1 (hp.1.dec τ).2 a ha⟩
  obtain ⟨y, hy, hyv⟩ := exists_multT_eq_poin hHC hCW hCRD D W.θ hθ (G.V (.core 0)) _ MP (G.sp.dec0.lat (L.ΛY 0) fun _ => 1)
    G.modul hsdV hmod p.v₀ hKD (p.g₀⁻¹ * stabilizerEmbedding G.sp.dec0 x⁻¹) ⟨D.eTau.symm 1⟩
  obtain ⟨v₀', hv₀'⟩ : ∃ v₀' : MP.Vec, ∀ τ, (v₀' τ : MP.H τ) = p.v₀ τ :=
    ⟨fun τ => ⟨p.v₀ τ, GlobalTheory.Core.Mi.kFin_le_sm hHC MP τ (hp.1.dec τ).1⟩, fun _ => rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : MP.Vec, ∀ τ, (a' τ : MP.H τ) = MP.rep τ (cmp W.θ τ p.g₀) (v₀' τ) :=
    ⟨fun τ => ⟨MP.rep τ (cmp W.θ τ p.g₀) (v₀' τ),
      GlobalTheory.UnifEvery.rep_mem_sm MP τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ _ p.g₀ τ) (v₀' τ).2⟩, fun _ => rfl⟩
  have hv₀f : (fun τ => (v₀' τ : MP.H τ)) = p.v₀ := funext hv₀'
  have hU := (mem_multT W.θ MP _ 1 y).1 hy
  have key := GlobalTheory.RealEquiv.mult_realElt D (G.V (.core 0)) _ W.θ MP _ 1 _ hU (fun τ => cmp W.θ τ p.g₀)
    (fun τ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ _ p.g₀ τ) v₀' a' ha'
  rw [← GlobalTheory.RealTransSm.eq_realElt hθ hp.1.real] at key
  have hyg : ∀ g, y (PiTensorProduct.tprod ℂ a') g =
      poin W.θ MP (congLev D.sp.cm (G.V (.core 0)).gram (G.sp.dec0.lat (L.ΛY 0) fun _ => 1) G.modul) (p.v W.θ)
        (stabilizerEmbedding G.sp.dec0 x⁻¹) (p.v W.θ) g := by
    intro g
    rw [apply_tprod_eq, key]
    show PiTensorProduct.lift.symm y v₀' (g * p.g₀) = _
    rw [← apply_tprod_eq, hyv v₀' (fun τ => (hv₀' τ).symm ▸ (hp.1.dec τ).1), hv₀f]
    exact GlobalTheory.T.coefficientPoincareSeries_move_real_point D W.θ hθ (G.V (.core 0)) _ MP _ p.v₀ p.g₀ hp.1.real _ g
  have hmem : y ∈ CoreForms G W.θ 0 MP := by
    show y ∈ MultT W.θ MP (Lev.levA (G.V (.core 0)) (G.levCong (.core 0)) : Set (GA D (G.V (.core 0)))) 1
    unfold GridData.levCong
    rw [hlam]
    exact hy
  have hper : per0 G M (y (PiTensorProduct.tprod ℂ a')) (t (PiTensorProduct.tprod ℂ p.w)) ≠ 0 := by
    unfold per0
    simp_rw [hyg]
    rw [hvμ, hv𝓕] at hne
    exact hne
  exact ⟨y, hmem, _, _, hper⟩

end UpperTheory.Lit.Cusp

end
end
end
