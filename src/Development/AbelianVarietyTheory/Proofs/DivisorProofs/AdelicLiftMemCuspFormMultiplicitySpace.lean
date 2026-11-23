module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VectorLevelCharacters
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalLevelFixesFockVectorsFiniteDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFockVectorHeisenbergAverageIsotropicEqZeroStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OneLeAPlLast
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOfOverK
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeight
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UniformModerateGrowthLevel
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorMixedLaplacianKilledLoweringKilled
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroupStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorFiniteDatumIsThetaVacuumOff
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaLiftLinearMapCuspFormMultiplicity
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModelHolomorphicOverReflexField

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem isEnum_unique {n : ℕ} {S : SPar} {lam lam' : Fin n → ℝ} {ε ε' : Fin n → Bool}
    (h : IsEnum S lam ε) (h' : IsEnum S lam' ε') : lam = lam' ∧ ε = ε' := by
  obtain ⟨hA, q, hq, hS⟩ := h
  obtain ⟨hA', q', hq', hS'⟩ := h'
  have hqA : StrictAnti q := fun a b hab => by
    have := hA hab; rw [hq, hq] at this; exact_mod_cast this
  have hqA' : StrictAnti q' := fun a b hab => by
    have := hA' hab; rw [hq', hq'] at this; exact_mod_cast this
  have himg : Finset.univ.image q = Finset.univ.image q' := by
    have e := congrArg (Finset.image Prod.fst) (hS.symm.trans hS')
    simpa [Finset.image_image, Function.comp_def] using e
  have hr : Set.range q = Set.range q' := by
    have := congrArg (fun s : Finset ℚ => (s : Set ℚ)) himg
    simpa [Finset.coe_image] using this
  have hqq : q = q' := (StrictAnti.range_inj hqA hqA').1 hr
  subst hqq
  refine ⟨funext fun a => by rw [hq, hq'], funext fun a => ?_⟩
  have hm : (q a, ε a) ∈ S := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
  rw [hS'] at hm
  obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hm
  have hb1 : b = a := hqA.injective (congrArg Prod.fst hb)
  subst hb1
  exact (congrArg Prod.snd hb).symm

theorem parAt_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ) (ρ : D.what₂.Tau) :
    parAt (Wc D i) σ ρ = parAt (Wc D i) (sg0 D A) (lab σ ρ) := by
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hsig : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) :=
    fun τ => D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hl := ((GlobalTheory.GalLift.labels_overK σ).1 hK).2 ρ
  unfold parAt kapAt
  rw [if_pos hl, hs, GlobalTheory.ThetaFiresProbe.lab_fixed, if_pos (GlobalTheory.ThetaFiresProbe.labE_fixed _), hsig ρ, hsig (lab σ ρ)]

theorem model_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ) (ρ : D.what₂.Tau) :
    (R.MW i σ).lam ρ = (R.MW i (sg0 D A)).lam (lab σ ρ) ∧ (R.MW i σ).ε ρ = (R.MW i (sg0 D A)).ε (lab σ ρ) := by
  have h1 := (R.MW i σ).enum ρ
  rw [parAt_overK R i σ hK ρ] at h1
  exact isEnum_unique h1 ((R.MW i (sg0 D A)).enum (lab σ ρ))

theorem holShape_overK : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F →
    ∀ i σ s, IsEmbOverK D σ s → HolShape (R.MW i σ) ∧ ∃ w, WtIs (R.MW i σ) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hc i σ s hE
  have hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ := hE.2
  obtain ⟨hH, w0, hw0⟩ := holShape_fixed D G Pl0 T A Ks R hc.models.order i
  have hm := model_overK R i σ hK
  refine ⟨fun ρ => ?_, fun ρ c => w0 (lab σ ρ) c, fun ρ c => ?_⟩
  · have h := hH (lab σ ρ)
    rw [← (hm ρ).1, ← (hm ρ).2] at h
    exact h
  · have h := hw0 (lab σ ρ) c
    unfold extWt at h ⊢
    rw [← (hm ρ).1, ← (hm ρ).2] at h
    exact h

end GlobalTheory.LowRow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModelHolomorphicOverReflexFieldStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.liftModel_holomorphic_overReflexField : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ i σ s, IsEmbOverK D σ s → HolShape (R.MW i σ) ∧ ∃ w, WtIs (R.MW i σ) w := by
  first | exact @GlobalTheory.LowRow.holShape_overK | exact GlobalTheory.LowRow.holShape_overK | (intros; apply GlobalTheory.LowRow.holShape_overK <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoweringPartKillsFockProductMinors

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowKillDelta

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis GlobalTheory.FockKill
open scoped Real Classical

section Model

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D} {τ : D.what₂.Tau}
  {Sp : D.what₂.Tau → SPar} {M : DSModel T Sp}

theorem exists_coef_any {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) {p : ℕ} {BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hBT : IsONBasis (gramAt D T τ) (cart M τ) (BT τ) p)
    {X : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (lX : X ∈ lieAt T τ) (lY : Complex.I • (cart M τ * X) ∈ lieAt T τ) (ha : cart M τ * X = -(X * cart M τ)) :
    ∃ ν : Fin T.rank → Fin T.rank → ℂ, (∀ a b : Fin T.rank, ¬ (p ≤ (a : ℕ) ∧ (b : ℕ) < p) → ν a b = 0) ∧
      ∀ a c b d, ∀ u, u = unitMap (BS τ) (BT τ) a c → ∀ u', u' = unitMap (BS τ) (BT τ) b d →
        ((omDir S T τ (X * u) τ u' : ℝ) + Complex.I * (omDir S T τ (cplxO 1 (cart M τ) (X * u)) τ u' : ℝ)) +
          (-Complex.I) * ((omDir S T τ (X * cplxO 1 (cart M τ) u) τ u' : ℝ) +
            Complex.I * (omDir S T τ (cplxO 1 (cart M τ) (X * cplxO 1 (cart M τ) u)) τ u' : ℝ)) =
        (if c = d then ν a b else 0) + (if d = c then ν b a else 0) := by
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  obtain ⟨ε, hε, -, ht⟩ := hBT
  let o : Matrix (Fin T.rank) (Fin T.rank) ℂ → Fin T.rank → Fin T.rank → ℝ := fun W a b =>
    2 * (tauE D τ D.host.xi0 * ((BT τ)ᴴ * gramAt D T τ * W * BT τ) a b).re
  have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
  have osym : ∀ W ∈ lieAt T τ, ∀ a b, o W a b = o W b a := fun W hW a b =>
    congrArg (2 * ·) (skew_entry (GlobalTheory.SmoothAutCheck.gramAt_herm T τ) hW hre a b)
  have ozero : ∀ W, cart M τ * W = -(W * cart M τ) → ∀ a b : Fin T.rank, ((a : ℕ) < p ↔ (b : ℕ) < p) →
      o W a b = 0 := fun W hW a b hab => by
    simp only [o]
    rw [zero_entry (hT τ) ht hW, mul_zero, Complex.zero_re, mul_zero]
    rcases hε a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hε b with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> simp only [h1, h3]
    · norm_num
    · exact absurd (hab.1 h2) (by omega)
    · exact absurd (hab.2 h4) (by omega)
    · norm_num
  have hom1 : ∀ W a c b d, omDir S T τ (W * unitMap (BS τ) (BT τ) a c) τ (unitMap (BS τ) (BT τ) b d) =
      if c = d then o W b a else 0 := fun W a c b d => by
    rw [omDir, if_pos rfl, trace_unitMap (hB τ)]
    split_ifs <;> simp [o]
  have hJ : ∀ (W : Matrix (Fin T.rank) (Fin T.rank) ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      cplxO 1 (cart M τ) (W * u) = Complex.I • (cart M τ * W) * u := fun W u => by
    rw [cplxO, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]
  have hJ' : ∀ u : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      X * cplxO 1 (cart M τ) u = (-(Complex.I • (cart M τ * X))) * u := fun u => by
    rw [cplxO, Matrix.mul_one, ha, smul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hJ'' : Complex.I • (cart M τ * -(Complex.I • (cart M τ * X))) = X := by
    rw [Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, (hT τ).1, Matrix.one_mul, smul_neg, smul_smul,
      Complex.I_mul_I, neg_smul, neg_neg, one_smul]
  have oneg : ∀ W a b, o (-W) a b = -o W a b := fun W a b => by
    simp only [o, Matrix.neg_mul, Matrix.neg_apply, mul_neg, Complex.neg_re]
  clear_value o
  refine ⟨fun a b => if p ≤ (a : ℕ) ∧ (b : ℕ) < p then
    2 * (o X a b + Complex.I * o (Complex.I • (cart M τ * X)) a b) else 0, fun a b h => if_neg h, ?_⟩
  rintro a c b d _ rfl _ rfl
  rw [hJ', hJ, hJ, hJ'', hom1, hom1, hom1, oneg]
  by_cases e3 : c = d
  swap
  · simp [e3, Ne.symm e3]
  subst e3
  simp only [if_true]
  have z1 := ozero _ ha
  have z2 := ozero _ (anti_I ha)
  have s1 := osym _ lX a b
  have s2 := osym _ lY a b
  generalize Complex.I • (cart M τ * X) = Y at z2 s2
  rw [s1, s2]
  have e : (o X b a : ℂ) + Complex.I * o Y b a + -Complex.I * ((-o Y b a : ℝ) + Complex.I * o X b a) =
      2 * (o X b a + Complex.I * o Y b a) := by
    push_cast
    linear_combination (-o X b a : ℂ) * Complex.I_mul_I

  rw [e]
  by_cases ha' : (a : ℕ) < p <;> by_cases hb' : (b : ℕ) < p
  · simp [z1 b a (by simp [ha', hb']), z2 b a (by simp [ha', hb'])]
  · rw [if_neg (by omega), if_pos (by omega), zero_add]
  · rw [if_pos (by omega), if_neg (by omega), add_zero]
  · simp [z1 b a (by simp [ha', hb']), z2 b a (by simp [ha', hb'])]

theorem gen_kill_any (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) {p : ℕ} {BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hBT : IsONBasis (gramAt D T τ) (cart M τ) (BT τ) p)
    {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} {GX GY : Module.End ℂ (WO S T → ℂ)}
    (hX : IsGen ψ om θ τ X GX) (hY : IsGen ψ om θ τ (Complex.I • (cart M τ * X)) GY)
    (lX : X ∈ lieAt T τ) (lY : Complex.I • (cart M τ * X) ∈ lieAt T τ) (ha : cart M τ * X = -(X * cart M τ))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f)
    (h0 : (GX + Complex.I • GY) f = 0) {P : MvPolynomial (FVar D T.rank S.rank) ℂ}
    (hP : ∀ a b : Fin T.rank, p ≤ (a : ℕ) → (b : ℕ) < p →
      ∑ c : Fin S.rank, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) P) = 0) :
    (GX + Complex.I • GY) (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (BT) f P) = 0 := by
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hS := fun τ => isCartanInv_one (hB τ)
  obtain ⟨ν, n0, hν⟩ := exists_coef_any hB hBT lX lY ha
  unfold pureTensorO aPlusAll
  refine (quad_pure (P := IsThetaFunO ψ S T) (G := GX + Complex.I • GY)
    (B := fun k g => ((fockScale D k.1 : ℂ)⁻¹ * (if k.1 = τ then (1 : ℂ) else 0)) •
      (annih (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) (X * unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g +
        (-Complex.I) • annih (heisO ψ S T) θ τ (cplxO 1 (cart M τ))
          (X * cplxO 1 (cart M k.1) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2)) g))
    (μ := fun i j => if i.1 = τ then if j.1 = τ then if i.2.2 = j.2.2 then
      ((fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * ν i.2.1 j.2.1 else 0 else 0 else 0)
    (fun _ _ => theta_add) (fun a _ => theta_smul a) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf ?_ h0 P).trans ?_
  · exact fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  · exact fun i j _ h => aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
  · exact fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  · exact fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  · intro i g g' hg hg'
    rw [annih_add hψ hθ _ _ _ hg hg', annih_add hψ hθ _ _ _ hg hg']
    simp only [smul_add]
    abel
  · intro i a g hg
    rw [annih_smul hψ hθ _ _ _ _ hg, annih_smul hψ hθ _ _ _ _ hg, smul_comm _ a, ← smul_add, smul_comm _ a]
  · rintro ⟨τ₁, a, c⟩ ⟨τ₂, b, d⟩ g hg
    have ta := fun z => annih_theta hψ hθ τ (cplxO 1 (cart M τ)) z hg
    have aa := fun z => annih_aPlus (sS := fun _ => 1) hψ hθ τ z hS hT τ₂ (unitMap (BS τ₂) (BT τ₂) b d) hg
    dsimp only at aa ⊢
    rw [aa, aa, aPlus_smul hψ hθ _ _ _ _ (theta_add (ta _) (theta_smul _ (ta _))),
      aPlus_add hψ hθ _ _ _ (ta _) (theta_smul _ (ta _)), aPlus_smul hψ hθ _ _ _ _ (ta _), smul_add (-Complex.I),
      add_add_add_comm, smul_add, smul_smul, ← add_smul, smul_smul]
    refine congrArg₂ (· + ·) rfl (congrArg (· • g) ?_)
    by_cases e1 : τ₁ = τ
    swap
    · simp only [if_neg e1, ite_self, mul_zero, zero_mul, add_zero]
    by_cases e2 : τ₂ = τ
    swap
    · simp [e2, omDir, Ne.symm e2]
    subst e1
    subst e2
    have := hν a c b d _ rfl _ rfl
    simp only [if_true]
    by_cases e3 : c = d
    · simp only [if_pos e3, if_pos e3.symm] at this ⊢
      linear_combination ((fockScale D τ₂ : ℂ)⁻¹ * (fockScale D τ₂ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * this
    · simp only [if_neg e3, if_neg (Ne.symm e3)] at this ⊢
      linear_combination ((fockScale D τ₂ : ℂ)⁻¹ * (fockScale D τ₂ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * this
  · exact fun i _ h => gen_aPlus hψ hθ hX hY _ _ _ h
  · intro i
    rw [hv, hv, smul_zero, add_zero, smul_zero]
  · refine (congrArg _ ?_).trans (map_zero _)
    simp only [Fintype.sum_prod_type, ite_smul, zero_smul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.smul_sum]
    by_cases hab : p ≤ (a : ℕ) ∧ (b : ℕ) < p
    · rw [hP a b hab.1 hab.2, smul_zero]
    · rw [n0 a b hab, mul_zero, zero_smul]

end Model

theorem rderC_theta_eq_zero_any : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → S.SigOK → T.SigOK → ∀ (BS : D.what₂.Tau → Mt S.rank), (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (p : D.what₂.Tau → ℕ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsONBasis (gramAt D T τ) (cart M τ) (BT τ) (p τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → ∀ (P : PolF D T.rank S.rank) τ, (∀ a b : Fin T.rank, p τ ≤ (a : ℕ) → (b : ℕ) < p τ → ∑ c : Fin S.rank, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) P) = 0) → ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS BT f P)) = 0 := by
  intro D ψ S T χS χT om hom θ hθ kS kT BS hBS Sp M p BT hBT f hf hv P τ hP Z hZ h
  have hψ := hom.std
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1 := fun τ => by
    obtain ⟨ε, h1, h2, -⟩ := hBS τ
    rw [h2, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases h1 a with h | h
    · rw [h.1, Complex.ofReal_one]
    · exact absurd a.2 (not_lt.2 h.2)
  have hS := fun τ => isCartanInv_one (hB τ)
  obtain ⟨h1, h2⟩ := pMinus_laws hZ
  obtain ⟨ha, eY⟩ := parts (GlobalTheory.SmoothAutCheck.gramAt_unit T τ) (hT τ) h1 h2
  obtain ⟨lX, lY⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
  unfold RderC
  unfold conjAt at lX lY ⊢
  rw [eY] at lY ⊢
  generalize (1 / 2 : ℂ) • (Z + -((gramAt D T τ)⁻¹ * Zᴴ * gramAt D T τ)) = X at ha lX lY
  obtain ⟨GX, hX⟩ : ∃ G, IsGen ψ om θ τ X G := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ _ lX
  obtain ⟨GY, hY⟩ : ∃ G, IsGen ψ om θ τ (Complex.I • (cart M τ * X)) G :=
    GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ _ lY
  have hφ : IsThetaFunO ψ S T (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS BT f P) :=
    pure_mem (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
      (fun _ _ h => aPlus_theta hψ hθ _ _ _ h) hf _
  have key := gen_kill_any hψ hθ hB (hBT τ) hX hY lX lY ha hf (hv τ)
    (gen_kill_vac hom hθ kS kT hS hT hX hY lX lY ha hf hv) hP
  generalize pureTensorO ψ θ S T (fun _ => 1) (cart M) BS BT f P = φ at key hφ
  funext g
  have a1 := ((hX φ hφ).2.2.2 (h, g) 0).deriv
  have a2 := ((hY φ hφ).2.2.2 (h, g) 0).deriv
  simp only [Prod.mk_mul_mk, mul_one] at a1 a2
  have a3 := congrFun (congrArg (om (h, g)) key) 0
  rw [LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul, map_zero] at a3
  simp only [Pi.add_apply, Pi.smul_apply, Rder, thetaKO]
  rw [a1, a2]
  exact a3

theorem rderC_ptAt_delta_eq_zero : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m om BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m om BW f₀ f c io → ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus (R.MW i σ) τ, ∀ h, RderC R.θ (Wc D i) τ Z (fun g => thetaKO om h g (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ BW f (deltaAtEmb D i σ))) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m om BW f₀ f c io hL τ Z hZ h
  obtain ⟨hCore, -, -, -, -, hW, hBW, hLV, -⟩ := id hL
  have hf := (GlobalTheory.FinZeta.levVec_vacFin R F i t σ s P cμ cη m om BW f₀ f c io hL).1
  obtain ⟨⟨hψ, hv⟩, e, he, hth⟩ := hLV
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hvac : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i σ) τ)) f := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hv.inf ho.conj.infPart_eq ho.conj.conj.infPart_eq hth hv.theta hf (hv.fock τ)
  have hpq : ∀ ρ, pW D i ρ + qW D i ρ ≤ (Vc D i).rank := fun ρ =>
    (sig_sum _ (D.sp.W_sig _) (tauE D ρ)).trans_le ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i))
  have hP := GlobalTheory.MinorHarmonic.laplacian_delta D (Wc D i).rank (Vc D i).rank (pW D i) (qW D i) (aPlAt D i σ) (aMiAt D i σ) hpq τ
  exact rderC_theta_eq_zero_any D R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) om hW R.θ hv.inf (D.sp.V_sig _) (D.sp.W_sig _)
    (R.BV i) (hCore.models.BV i) _ (R.MW i σ) (pW D i) BW hBW f hf hvac (deltaAtEmb D i σ) τ hP Z hZ h

end GlobalTheory.LowKillDelta
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoweringPartKillsFockProductMinorsStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.lowering_part_kills_fock_product_minors : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m om BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m om BW f₀ f c io → ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus (R.MW i σ) τ, ∀ h, RderC R.θ (Wc D i) τ Z (fun g => thetaKO om h g (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ BW f (deltaAtEmb D i σ))) = 0 := by
  first | exact @GlobalTheory.LowKillDelta.rderC_ptAt_delta_eq_zero | exact GlobalTheory.LowKillDelta.rderC_ptAt_delta_eq_zero | (intros; apply GlobalTheory.LowKillDelta.rderC_ptAt_delta_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLiftMemCuspFormMultiplicitySpace

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.CuspLift

theorem liftIsCuspC : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), LiftIsCuspC R F := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F
  intro i t σ s P cμ cη m ω BW f₀ f c io hd ν 𝓕 hν φ hφ
  obtain ⟨hcore, -, hemb, -, -, hom, -, -, hpt, hc, hio⟩ := id hd
  have h5 := GlobalTheory.Core5.of_core hcore
  have hm := h5.models
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨hM, w, hw⟩ := GlobalTheory.T.liftModel_holomorphic_overReflexField R F h5 i σ s hemb
  have : IsTopologicalGroup (GA D (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hF := GlobalTheory.ThetaIntegrand.form_continuous (finHom (Vc D i)).rangeRestrict (GQ (Vc D i)) c.ρ hc.2.2.1
    (eventually_grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) hφ
  have key := GlobalTheory.DefLift.ThetaMap.exists_member hP hom hm.inf hpos hM hw hc
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) BW f) hpt hio
    (GlobalTheory.T.lowering_part_kills_fock_product_minors R F i t σ s P cμ cη m ω BW f₀ f c io hd)
    (J := levS _ (R.βW i) (R.datWp i R.triv)) (fun _ hk => hk.1) (GlobalTheory.DefLift.ThetaMap.level_open _ _ _)
    (fun k hk Q => GlobalTheory.PrincipalLevelFock.levW_fix_ptAt R F i t σ s P cμ cη m ω BW f₀ f c io hd Q k hk)
    (GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters.principalLevelCharacter_eq_one R i)
    (fun Q h g ξ hξ => GlobalTheory.T.levelFockVector_heisenbergAverage_isotropic_eq_zero R F i t σ s P cμ cη m ω BW f₀ f c io hd Q h g ξ hξ)
    hF (GlobalTheory.ThetaIntegrand.ext_invariant c hφ) hν.1.1 hν.2
  obtain ⟨Θ, hΘ, hΘv⟩ := key
  refine ⟨Θ, Submodule.subset_span hΘ, fun v g => ?_⟩
  rw [hΘv v]
  rfl

end GlobalTheory.LowRow.CuspLift

end
end
end
