module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModelStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnMapEqRootExchangeOperatorTranslate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalZetaIntegralOpenSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergInvariantFactorsContraction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModelStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapContractionSupportFinitelyManyCellsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelWeilOperatorTrivialAtPlaceIsModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBesselStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportLevelPlaceSymmetricChainSecondHalf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontriviaStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiFlatMapSupportFiniteCells

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.LocFlat.CellSupport

theorem det_colE {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (β : n → k) :
    Matrix.GeneralLinearGroup.det (colE c p β) = 1 := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, colE, upU, Matrix.det_fromBlocks_zero₂₁]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_inv_of_det_one {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL b k) (hg : Matrix.GeneralLinearGroup.det g = 1) (Ψ : Matrix b a k → ℂ) :
    om μ (1 : GL a k) g⁻¹ Ψ = fun z => Ψ (g.val * z) := by
  funext z
  simp only [om, map_inv, hg, inv_one, map_one, nabs_one, inv_inv, Real.one_rpow, Units.val_one, Complex.ofReal_one,
    one_mul, Matrix.mul_one]

theorem om_eq_mul_om_triv {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (h : GL b k) (Ψ : Matrix b a k → ℂ) :
    om μ (1 : GL a k) h Ψ = fun z => (((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) * om 1 (1 : GL a k) h Ψ z := by
  funext z
  simp only [om, map_one, MonoidHom.one_apply, inv_one, Units.val_one]
  ring

theorem opE_const_mul [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {c : ℕ} (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (s : ℂ)
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν p (fun z => s * Ψ z) x₀ = s * opE ψ ν p Ψ x₀ := by
  unfold opE
  rw [← integral_const_mul]
  simp only [mul_assoc]

end GlobalTheory.LocFlat.CellSupport

namespace GlobalTheory.LocFlat
open GlobalTheory.LocFlat.CellSupport

theorem flCol_support_finite_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (ν : Measure k),
    ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p →
    p ≤ c → ∀ (μ : kˣ →* ℂˣ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsOpen (J : Set (GL (n ⊕ Fin c) k)) →
    ∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (a : GL (n' ⊕ Fin (c + 1)) k),
    ∃ T : Finset (GL (n ⊕ Fin c) k), ∀ x : GL (n ⊕ Fin c) k, GlobalTheory.LocFlat.flCol ψ ν p (om μ a x Φ.1) ≠ 0 →
      ∃ β : n → k, ∃ r ∈ R k n c p, ∃ t ∈ T, ∃ j ∈ J, x = colE c p β * r * t * j := by
  intro k _ _ _ _ _ _ ψ hψc hψ ν hν n n' _ _ _ _ c p hp1 hpc μ J hJ Φ a
  obtain ⟨T, -, hT⟩ := GlobalTheory.PosOne.covers_opE_finite k n n' c p hp1 hpc ψ hψc hψ ν 1
    (by rw [MonoidHom.ker_one]; exact isOpen_univ) J hJ ⟨om μ a 1 Φ.1, om_mem_SB μ a 1 Φ.2⟩
  refine ⟨T, fun x hx => ?_⟩
  obtain ⟨X, hX⟩ := Function.ne_iff.1 hx
  rw [flCol_eq_opE_colE k ψ ν hψc hν n n' c p hp1 hpc _ (om_mem_SB μ a x Φ.2) X] at hX
  set β : n → k := fun r => X r (Sum.inr ()) with hβ
  replace hX : opE ψ ν p (om μ 1 (colE c p β)⁻¹ (om μ a x Φ.1)) X.toCols₁ ≠ 0 := by
    rw [om_inv_of_det_one μ _ (det_colE c p β)]
    exact hX
  rw [← om_mul] at hX
  have e : om μ (1 * a) ((colE c p β)⁻¹ * x) Φ.1 = om μ 1 ((colE c p β)⁻¹ * x) (om μ a 1 Φ.1) := by
    rw [← om_mul, mul_one]
  rw [e, om_eq_mul_om_triv, opE_const_mul] at hX
  obtain ⟨t, ht, hd⟩ := hT ((colE c p β)⁻¹ * x) (Function.ne_iff.2 ⟨X.toCols₁, right_ne_zero_of_mul hX⟩)
  obtain ⟨r, hr, j, hj, hx'⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hd.symm
  refine ⟨β, r, hr, t, ht, j, hj, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_assoc r, ← hx', mul_inv_cancel_left]

end GlobalTheory.LocFlat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiFlatMapSupportFiniteCellsStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.fourierJacobi_flatMap_support_finite_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (ν : Measure k),
    ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p →
    p ≤ c → ∀ (μ : kˣ →* ℂˣ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsOpen (J : Set (GL (n ⊕ Fin c) k)) →
    ∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (a : GL (n' ⊕ Fin (c + 1)) k),
    ∃ T : Finset (GL (n ⊕ Fin c) k), ∀ x : GL (n ⊕ Fin c) k, GlobalTheory.LocFlat.flCol ψ ν p (om μ a x Φ.1) ≠ 0 →
      ∃ β : n → k, ∃ r ∈ R k n c p, ∃ t ∈ T, ∃ j ∈ J, x = colE c p β * r * t * j := by
  first | exact @GlobalTheory.LocFlat.flCol_support_finite_cells | exact GlobalTheory.LocFlat.flCol_support_finite_cells | (intros; apply GlobalTheory.LocFlat.flCol_support_finite_cells <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergInvariantFactorsContractionStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.heisenbergInvariant_factors_contraction : GlobalTheory.LocFlat.ContrFactor := by
  first | exact @GlobalTheory.LocFlat.contrFactor | exact GlobalTheory.LocFlat.contrFactor | (intros; apply GlobalTheory.LocFlat.contrFactor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepFinitelyManyCellsUniformProo

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl.FinOneProof



theorem finOne : ∀ D : D7, FinOne D := by
  intro D ψ hstd σ S Q a
  have hOm := GlobalTheory.T.weilDatum_localModel_formula D
  have hFL := GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D
  have hFLs := GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D
  have hBF := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D hFL hFLs hOm
  have hFB := GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel D hFL hFLs hOm
  have hCo := GlobalTheory.T.lineContraction_splitPlace_localModel D GlobalTheory.T.heisenbergInvariant_factors_contraction
  obtain ⟨-, hchar, hxi, -, hcomp⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D Q.k (ofSplit Q.q) ψ hstd
  obtain ⟨hψc, hψ1⟩ := hchar Q.ψk Q.char
  haveI := Q.unitVol.1
  have hsd : IsSelfDual Q.ψk Q.ν := isSelfDual_of_isUnitVol Q.ν Q.cond Q.unitVol
  have hc : Q.c = 2 * σ := by have := Q.F.bes.1; omega
  obtain ⟨μV, hμV⟩ := hcomp S.s₁.χV
  obtain ⟨μW, hμW⟩ := hcomp S.s₁.χW
  obtain ⟨μV', hμV'⟩ := hcomp S.s₂.χV
  obtain ⟨μW', hμW'⟩ := hcomp S.s₂.χW
  obtain ⟨C₀, hC₀⟩ := ((GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace D Q.k (ofSplit Q.q) _ (σ + 1) Q.F.s Q.F.s_ne).1 S.B Q.F.F₀).1
  obtain ⟨C₂, hC₂⟩ := ((GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace D Q.k (ofSplit Q.q) _ σ (Q.F.s * (ofSplit Q.q).xi)
    (mul_ne_zero Q.F.s_ne hxi)).1 S.B' Q.F.F₂).1
  have hsb := GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective Q.k Q.ψk Q.ν hψc inferInstance
  have hjac' : (ofSplit Q.q).IsJacFrame S.J Q.F.s (-(ofSplit Q.q).xi ^ 2 * (ofSplit Q.q).hz S.B') Q.F.F₁ Q.F.G₁ :=
    GlobalTheory.LocMod.GSuppTwo.hz_link (ofSplit Q.q) S.l ▸ Q.F.jac

  let ca : ℂ := (((μV * μW⁻¹) (Matrix.GeneralLinearGroup.det a) : ℂˣ) : ℂ)
  let Φa : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) := ca • Q.Φ₁

  let cx : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → ℂ := fun x => (((μV' * μW'⁻¹) (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)
  let Φx : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) :=
    fun x => cx x • Q.Φ₂

  have step₁ : ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v),
      ∀ x, ∃ U, (ofSplit Q.q).IsModel ψ C₀ Q.F.F₁ U ∧ ∀ Ψ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k),
        Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) (om μV⁻¹ a x Φa.1) →
        flatBF S.s₁ (S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) (comb ψ _ _ Q.D₁ f₁)) = U Ψ := by
    intro f₁ f₂ hvac g hg h₁ hh₁ x
    obtain ⟨⟨Tm, O, hTm, hO, hTO⟩, -⟩ := hvac
    have hcomb : comb ψ _ _ Q.D₁ f₁ = Tm Q.Φ₁ := by
      rw [← hTO]; exact (Q.dat₁.2 Tm hTm O Q.Φ₁ hO rfl).symm
    let Φ' : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) :=
      ⟨om μV⁻¹ a x Φa.1, om_mem_SB _ _ _ Φa.2⟩
    have hloc : S.s₁.om (Q.gl₀ a, Q.gl₁ x) (Tm Q.Φ₁) = Tm Φ' :=
      hOm Q.k (ofSplit Q.q) ψ S.B.V S.J.W S.s₁.χV S.s₁.χW S.s₁.om S.s₁.weil μV μW hμV hμW _ _ Q.F.G₀ Q.F.G₁ Tm hTm
        (Q.gl₀ a) a (Q.gl₁ x) x (Q.loc₀ a) (Q.loc₁ x) Q.Φ₁ Φ' (by
          funext z; simp only [Φ', Φa, ca, om, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring)
    have hmod := GlobalTheory.LocModMove.isModel_weil_off D Q.k Q.q ψ hstd S.B.V S.J.W _ _ S.s₁.om S.s₁.weil _ _ Q.F.G₀ Q.F.G₁
      Tm hTm g hg h₁ hh₁
    obtain ⟨U, hU, hflat⟩ := hBF Q.k (ofSplit Q.q) Q.ν inferInstance ψ Q.ψk Q.char (σ + 1) S.B S.J S.s₁ Q.F.s Q.F.s_ne _ _
      (Q.c + 1 + 1) Q.F.F₀ C₀ Q.F.G₀ Q.F.F₁ Q.F.G₁ hC₀ Q.F.bes Q.F.jac _ hmod
    refine ⟨U, hU, fun Ψ hΨ => ?_⟩
    have hm : S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) = S.s₁.om (g, h₁) * S.s₁.om (Q.gl₀ a, Q.gl₁ x) := by
      rw [← map_mul, Prod.mk_mul_mk]
    rw [hcomb, hm, Module.End.mul_apply, hloc]
    exact hflat Φ' Ψ hΨ

  have step₂ : ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v),
      ∀ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (· = Q.q.v), ∀ x y, ∃ U, (ofSplit Q.q).IsModel ψ Q.F.F₁ C₂ U ∧
        ∀ Ψ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k), Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) (om μV'⁻¹ x y (Φx x).1) →
        flatFB S.s₂ (S.s₂.om (h₁ * Q.gl₁ x, h₂ * Q.gl₂ y) (comb ψ _ _ Q.D₂ f₂)) = U Ψ := by
    intro f₁ f₂ hvac h₁ hh₁ h₂ hh₂ x y
    obtain ⟨-, ⟨Tm, O, hTm, hO, hTO⟩⟩ := hvac
    have hcomb : comb ψ _ _ Q.D₂ f₂ = Tm Q.Φ₂ := by
      rw [← hTO]; exact (Q.dat₂.2 Tm hTm O Q.Φ₂ hO rfl).symm
    let Φ' : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) :=
      ⟨om μV'⁻¹ x y (Φx x).1, om_mem_SB _ _ _ (Φx x).2⟩
    have hloc : S.s₂.om (Q.gl₁ x, Q.gl₂ y) (Tm Q.Φ₂) = Tm Φ' :=
      hOm Q.k (ofSplit Q.q) ψ S.J.W S.B'.V S.s₂.χV S.s₂.χW S.s₂.om S.s₂.weil μV' μW' hμV' hμW' _ _ Q.F.G₁ Q.F.G₂ Tm hTm
        (Q.gl₁ x) x (Q.gl₂ y) y (Q.loc₁ x) (Q.loc₂ y) Q.Φ₂ Φ' (by
          funext z; simp only [Φ', Φx, cx, om, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring)
    have hmod := GlobalTheory.LocModMove.isModel_weil_off D Q.k Q.q ψ hstd S.J.W S.B'.V _ _ S.s₂.om S.s₂.weil _ _ Q.F.G₁ Q.F.G₂
      Tm hTm h₁ hh₁ h₂ hh₂
    obtain ⟨U, hU, hflat⟩ := hFB Q.k (ofSplit Q.q) Q.ν inferInstance ψ Q.ψk Q.char σ S.J S.B' S.s₂ Q.F.s Q.F.s_ne _ _
      (Q.c + 1) Q.F.F₁ Q.F.G₁ Q.F.F₂ C₂ Q.F.G₂ hjac' hC₂ Q.F.bes' _ hmod
    refine ⟨U, hU, fun Ψ hΨ => ?_⟩
    have hm : S.s₂.om (h₁ * Q.gl₁ x, h₂ * Q.gl₂ y) = S.s₂.om (h₁, h₂) * S.s₂.om (Q.gl₁ x, Q.gl₂ y) := by
      rw [← map_mul, Prod.mk_mul_mk]
    rw [hcomb, hm, Module.End.mul_apply, hloc]
    exact hflat Φ' Ψ hΨ
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.T.fourierJacobi_flatMap_support_finite_cells Q.k Q.ψk hψc hψ1 Q.ν inferInstance Q.n₁ Q.n₀ (Q.c + 1 + 1) (σ + 1 + 1) (by omega) (by omega)
    μV⁻¹ Q.L₁.J Q.co₁.1 Φa a
  refine ⟨T₁, ?_, ?_⟩
  · intro f₁ f₂ hvac g hg h₁ hh₁ x hne
    obtain ⟨U, -, hU⟩ := step₁ f₁ f₂ hvac g hg h₁ hh₁ x
    let Ψ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) :=
      ⟨_, ((hsb _ _ (Q.c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 _ (om_mem_SB μV⁻¹ a x Φa.2)⟩
    rw [hU Ψ rfl] at hne
    have hne' : GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) (om μV⁻¹ a x Φa.1) ≠ 0 := by
      intro h0
      apply hne
      have : Ψ = 0 := Subtype.ext h0
      rw [this, map_zero]
    obtain ⟨β, r, hr, t, ht, j, hj, hx⟩ := hT₁ x hne'
    refine ⟨t, ht, colE (Q.c + 1 + 1) (σ + 1 + 1) β * r, ?_, j, hj, hx⟩
    exact (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D Q.k (ofSplit Q.q)).2.1 Q.n₁ (Q.c + 1 + 1) (σ + 1) S.J Q.F.s _ Q.F.F₁ Q.F.G₁ Q.F.jac _ β r hr
      (Q.loc₁ _)
  · intro x
    obtain ⟨T₂, hT₂⟩ := GlobalTheory.T.localFlatMapContraction_support_finitelyManyCells Q.k Q.ψk hψc hψ1 Q.ν hsd Q.n₀ Q.n₁ Q.n₂ (Q.c + 1) (σ + 1) (by omega) μV⁻¹ μV'⁻¹
      Q.L₂.J Q.co₂.1 Φa (Φx x) a x
    refine ⟨T₂, ?_⟩
    intro f₁ f₂ hvac g hg h₁ hh₁ h₂ hh₂ y hne
    obtain ⟨U₁, hU₁, hf₁⟩ := step₁ f₁ f₂ hvac g hg h₁ hh₁ x
    obtain ⟨U₂, hU₂, hf₂⟩ := step₂ f₁ f₂ hvac h₁ hh₁ h₂ hh₂ x y
    let Ψ₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) :=
      ⟨_, ((hsb _ _ (Q.c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 _ (om_mem_SB μV⁻¹ a x Φa.2)⟩
    let Ψ₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) :=
      ⟨_, ((hsb _ _ (Q.c + 1) (σ + 1) (by omega)).2 (by omega)).1 _ (om_mem_SB μV'⁻¹ x y (Φx x).2)⟩
    obtain ⟨Λ, -, hΛ⟩ := hCo Q.k (ofSplit Q.q) Q.ν inferInstance ψ hstd Q.ψk Q.char (σ + 1) σ S.B S.B' S.l S.J.W₀ S.vL
      Q.F.s Q.F.s_ne _ _ _ Q.F.F₀ C₀ Q.F.F₁ Q.F.F₂ C₂ hC₀ hC₂ U₁ U₂ hU₁ hU₂
    obtain ⟨Ξ, hΞ, hΞΛ⟩ := hΛ Ψ₁ Ψ₂
    unfold Dbl2.con at hne
    rw [hf₁ Ψ₁ rfl, hf₂ Ψ₂ rfl, hΞΛ] at hne
    have hne' : GlobalTheory.LocFlat.contr Q.ψk Q.ν (GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) (om μV⁻¹ a x Φa.1))
        (GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) (om μV'⁻¹ x y (Φx x).1)) ≠ 0 := by
      intro h0
      apply hne
      have : Ξ = 0 := Subtype.ext (hΞ.trans h0)
      rw [this, map_zero]
    obtain ⟨r, hr, t, ht, j, hj, hy⟩ := hT₂ y hne'
    exact ⟨t, ht, r, (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D Q.k (ofSplit Q.q)).2.2 Q.n₂ (Q.c + 1) σ S.B' (Q.F.s * (ofSplit Q.q).xi) Q.F.F₂ Q.F.G₂
      Q.F.bes' _ r hr (Q.loc₂ r), j, hj, hy⟩

end GlobalTheory.QPl.FinOneProof
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepFinitelyManyCellsUniformProoStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlaceDoubleStepFinitelyManyCellsUniform_proof : ∀ D : D7, FinOne D := by
  first | exact @GlobalTheory.QPl.FinOneProof.finOne | exact GlobalTheory.QPl.FinOneProof.finOne | (intros; apply GlobalTheory.QPl.FinOneProof.finOne <;> assumption)
end
end
