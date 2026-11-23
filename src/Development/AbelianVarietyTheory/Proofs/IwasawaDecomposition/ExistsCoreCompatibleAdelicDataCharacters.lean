module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
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
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeChar
public import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDictionaryCoreLawsBaseFrameChangeStatement
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ConjModelCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothModelsOnThetaTargets
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddingsStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_conjugate_reference_characters_good_embeddings : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), T.Q.Pins → AlgTie T → R.toLevCh.Is A.μ0 → ValKs R → ∃ (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle), (∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ChiAt R i σ (chiW ((i : ℕ) + 1) (res T σ))) ∧ ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj T.σ₀ σ (chiW j T.σ₀) (chiW j σ) := by
  first | exact @GlobalTheory.ConjRefChar.exists_chiAt | exact GlobalTheory.ConjRefChar.exists_chiAt | (intros; apply GlobalTheory.ConjRefChar.exists_chiAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreLawsForReplacedHeckeCharacters

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

section Change

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  {K : Type} [Field K] {C : Type} [AddCommGroup C] [Module K C] {σ : K →+* ℂ} {V : HSp D}
  {X : Comp → Data E r} {rd : C →ₛₗ[σ] FDSec X} {dict : GA D V → Σ c, Frame (X c).Ψ r} {mu mu' : GA D V → ℂ}

theorem norm_jFn_eq_of_muUnit (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (f : C) (q : AutQ V) :
    ‖jFn V σ rd dict mu' f q‖ = ‖jFn V σ rd dict mu f q‖ := by
  show ‖mu' q.out * rd f (dict q.out).1 (dict q.out).2‖ = ‖mu q.out * rd f (dict q.out).1 (dict q.out).2‖
  rw [norm_mul, norm_mul, h.2.1, h'.2.1]

theorem jMemL2_of_muUnit (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (hc : Continuous mu)
    (hc' : Continuous mu') (hL : JMemL2 V σ rd dict mu) : JMemL2 V σ rd dict mu' := by
  intro f
  have hne : ∀ g, mu g ≠ 0 := fun g h0 => by
    have := h.2.1 g
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hinv : ∀ γ ∈ GQ V, ∀ g, (fun g => mu' g / mu g) (γ * g) = (fun g => mu' g / mu g) g := by
    intro γ hγ g
    show mu' (γ * g) / mu (γ * g) = mu' g / mu g
    rw [h.1, h'.1, h.2.2.1 γ hγ, h'.2.2.1 γ hγ, one_mul, one_mul]
  have hm : AEStronglyMeasurable (onQ V (fun g => mu' g / mu g)) (muQ1 V) := by
    haveI : BorelSpace (GA D V) := ⟨rfl⟩
    rw [onQ_eq_lift _ hinv]
    refine Measurable.aestronglyMeasurable ?_
    exact measurable_from_quotient.2 (hc'.div hc hne).measurable
  have he : jFn V σ rd dict mu' f = onQ V (fun g => mu' g / mu g) * jFn V σ rd dict mu f := by
    funext q
    show mu' q.out * rd f (dict q.out).1 (dict q.out).2 =
      mu' q.out / mu q.out * (mu q.out * rd f (dict q.out).1 (dict q.out).2)
    rw [← mul_assoc, div_mul_cancel₀ _ (hne _)]
  refine (hL f).congr_norm ?_ (Filter.Eventually.of_forall fun q => (norm_jFn_eq_of_muUnit h h' f q).symm)
  rw [he]
  exact hm.mul (hL f).aestronglyMeasurable

theorem peterson_norm_independent_of_unitary_character (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (hL : JMemL2 V σ rd dict mu)
    (hL' : JMemL2 V σ rd dict mu') (f : C) : l2NormAlt V σ rd dict mu' hL' f = l2NormAlt V σ rd dict mu hL f := by
  show ‖(hL' f).toLp _‖ = ‖(hL f).toLp _‖
  rw [Lp.norm_toLp, Lp.norm_toLp,
    eLpNorm_congr_norm_ae (hL' f).aestronglyMeasurable (hL f).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => norm_jFn_eq_of_muUnit h h' f q)]

end Change

theorem exists_mu_reCore : ∀ (D : D7) (T : CoreJ D) (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle), LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj T.σ₀ σ (chiW j T.σ₀) (chiW j σ)) → ∃ mu, LawsJ (reCore T T.dict mu chiW T.x₀ T.cE) ∧ LawsCore (reCore T T.dict mu chiW T.x₀ T.cE).toCore := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro D T chiW hJ hC hchi
    have hex : ∀ j σ, ∃ mu : GA D (T.V j σ) → ℂ, InR D j → GoodEmb T.Q.c σ →
        MuVal (T.V j σ) (chiW j σ) mu ∧ MuUnit (T.V j σ) (T.dict j σ) mu ∧ Continuous mu := by
      intro j σ
      by_cases h : InR D j ∧ GoodEmb T.Q.c σ
      · obtain ⟨mu, h1, h2, h3, h4, h5⟩ := GlobalTheory.Member.exists_muVal D (T.V j σ) (chiW j σ) (hchi j h.1 σ h.2).1
          (hchi j h.1 σ h.2).2.1
        exact ⟨mu, fun hj hσ => ⟨h1, ⟨h2, h3, h4, (hJ.muUnit j hj σ hσ).2.2.2⟩, h5⟩⟩
      · exact ⟨fun _ => 1, fun hj hσ => absurd ⟨hj, hσ⟩ h⟩
    choose mu hmu using hex
    have hL : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CuspL2 (T.U j) σ (T.V j σ) (T.dict j σ) (mu j σ) :=
      fun j hj σ hσ a n hd => jMemL2_of_muUnit (hJ.muUnit j hj σ hσ) (hmu j σ hj hσ).2.1 (hJ.muCont j hj σ hσ)
        (hmu j σ hj hσ).2.2 (hJ.cuspidalL2Subspace j hj σ hσ a n hd)
    have hLM : LawsM (reCore T T.dict mu chiW T.x₀ T.cE).toCore :=
      { pins := hJ.pins
        half := hJ.half
        evalWD := hJ.evalWD
        unf := hJ.unf
        unTest := hJ.unTest
        chiTriv := hJ.chiTriv
        dictU := hJ.dictU
        spaceW := hJ.spaceW
        levelK := hJ.levelK
        xiAbs := hJ.xiAbs
        muUnit := fun j hj σ hσ => (hmu j σ hj hσ).2.1
        muCont := fun j hj σ hσ => (hmu j σ hj hσ).2.2
        finVol := hJ.finVol
        cuspFD := hJ.cuspFD
        supDef := hJ.supDef
        cuspidalL2Subspace := hL
        l2Def := fun j hj σ hσ a n hd f h0 => hJ.l2Def j hj σ hσ a n hd f
          ((peterson_norm_independent_of_unitary_character (hJ.muUnit j hj σ hσ) (hmu j σ hj hσ).2.1 (hJ.cuspidalL2Subspace j hj σ hσ a n hd)
            (hL j hj σ hσ a n hd) f).symm.trans h0)
        unitIndep := hJ.unitIndep
        ptNe := hJ.ptNe }
    refine ⟨mu, ?_, ?_⟩
    · exact
        { toLawsM := hLM
          cUnit := hJ.cUnit
          muVal := fun j hj σ hσ => (hmu j σ hj hσ).1
          muConj := fun j hj σ hσ => (hchi j hj σ hσ).2.2
          intAll := hJ.intAll
          modelW := hJ.modelW
          familyUniformisationBasePointOrthogonal := hJ.familyUniformisationBasePointOrthogonal
          kfHalf := hJ.kfHalf
          adPin := hJ.adPin }
    · exact
        { toLawsM := hLM
          cuspMul := hC.cuspMul
          latZ := hC.latZ
          cuNe := hC.cuNe
          expo := hC.expo }

end GlobalTheory.RealGeo
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreLawsForReplacedHeckeCharactersStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_core_laws_for_replaced_hecke_characters : ∀ (D : D7) (T : CoreJ D) (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle), LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj T.σ₀ σ (chiW j T.σ₀) (chiW j σ)) → ∃ mu, LawsJ (reCore T T.dict mu chiW T.x₀ T.cE) ∧ LawsCore (reCore T T.dict mu chiW T.x₀ T.cE).toCore := by
  first | exact @GlobalTheory.RealGeo.exists_mu_reCore | exact GlobalTheory.RealGeo.exists_mu_reCore | (intros; apply GlobalTheory.RealGeo.exists_mu_reCore <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodEmbeddingLabelIff

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem good_iff_labE_and_lab_conj :
    ∀ (D : D7) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL], LawsJ T → AlgTie T → ∀ (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), (GoodEmb T.Q.c (res T σ) ↔ labE σ (lab σ ρ) = tauE D ρ) ∧ lab ((starRingEnd ℂ).comp σ) ρ = lab σ ρ :=
  fun _ T _ hl ha σ ρ => ⟨GlobalTheory.ConjReading.branch_of_pins T ha hl.pins σ ρ, GlobalTheory.ConjReading.lab_conj σ ρ⟩

end GlobalTheory.HolRead
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalBaseFramesFlagDomainModels

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo.BaseFrame

variable {D : D7}

theorem tauE_injective : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem gram_x0Mat {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {r : ℕ} (hr : V.rank = r) (ρ : D.what₂.Tau)
    {p q : ℕ} (hpq : r = p + q) (hε : ∀ a, M.ε ρ a = decide ((a : ℕ) < p)) :
    ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
      (Matrix.reindex (finCongr hr) (finCongr hr) (x0Mat M ρ)) =
      Matrix.diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ) := by
  subst hr
  have hp : p ≤ V.rank := by omega
  have hq : nNeg (M.ε ρ) = q := (nNeg_shape hp hε).trans (by omega)
  have h0 : ∀ x : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-V.gramᵀ) x = (-(xᴴ * gramAt D V ρ * x))ᵀ := fun x => by
    ext a b
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, transpose_apply, Matrix.neg_apply, Matrix.mul_apply,
      conjTranspose_apply, gramAt, map_apply, map_neg, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [RCLike.star_def]
    ring
  have hinv : M.fr ρ * (M.fr ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ))
  have h1 : ((M.fr ρ)⁻¹)ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹ = Formalism.REAL.Jm (M.ε ρ) := by
    rw [← M.fr_gram ρ]
    calc _ = (M.fr ρ * (M.fr ρ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε ρ) * (M.fr ρ * (M.fr ρ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hinv]; simp
  have h2 : (x0Mat M ρ)ᴴ * gramAt D V ρ * x0Mat M ρ =
      (((M.fr ρ)⁻¹)ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹).submatrix (arr (nNeg (M.ε ρ))) (arr (nNeg (M.ε ρ))) := rfl
  show ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-V.gramᵀ) (x0Mat M ρ) = _
  rw [h0, h2, h1, hq]
  ext a c
  have ha := a.2
  have hc := c.2
  simp only [transpose_apply, Matrix.neg_apply, submatrix_apply, Formalism.REAL.Jm, diagonal_apply, hε, sgn, arr, Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

theorem exists_baseFrame : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → AlgTie T → FrameKs T.Q.c.F R.MW → ∃ (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), (∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (x₀ ((i : ℕ) + 1) (res T σ))) ∧ ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ) := by
  intro D G _ _ Pl0 T0 A T _ R hL hA hF
  classical
  let x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ := fun j s τ =>
    if h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau, j = (p.1 : ℕ) + 1 ∧ s = res T p.2.1 ∧ τ = tauE D p.2.2 then
      Matrix.reindex (finCongr (rank_Wc h.choose.1)) (finCongr (rank_Wc h.choose.1))
        (x0Mat (R.MW h.choose.1 h.choose.2.1) h.choose.2.2)
    else T.x₀ j s τ
  have key : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (x₀ ((i : ℕ) + 1) (res T σ)) := by
    intro i σ ρ
    have h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
        (i : ℕ) + 1 = (p.1 : ℕ) + 1 ∧ res T σ = res T p.2.1 ∧ tauE D ρ = tauE D p.2.2 := ⟨(i, σ, ρ), rfl, rfl, rfl⟩
    have aux : ∀ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
        ((i : ℕ) + 1 = (p.1 : ℕ) + 1 ∧ res T σ = res T p.2.1 ∧ tauE D ρ = tauE D p.2.2) →
        Matrix.reindex (finCongr (rank_Wc p.1)) (finCongr (rank_Wc p.1)) (x0Mat (R.MW p.1 p.2.1) p.2.2) =
          Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (x0Mat (R.MW i σ) ρ) := by
      rintro ⟨i', σ', ρ'⟩ ⟨h1, h2, h3⟩
      obtain rfl : i = i' := Fin.ext (Nat.add_right_cancel h1)
      obtain rfl : ρ = ρ' := tauE_injective h3
      rw [hF.1 i σ σ' h2 ρ]
    exact (dif_pos h).trans (aux _ h.choose_spec)
  refine ⟨x₀, fun i σ _ => key i σ, fun j hj s hs k τ hτ => ?_⟩
  by_cases h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
      j = (p.1 : ℕ) + 1 ∧ s = res T p.2.1 ∧ τ = tauE D p.2.2
  · obtain ⟨⟨i, σ, ρ⟩, rfl, rfl, rfl⟩ := h
    dsimp only at hj hs k hτ ⊢
    have hU := hL.unf _ hj _ hs
    have hdp : (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 := (hL.pins.2.2.2 _ hj).1
    have hM : ModelW (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) (res T σ)).X k) := by
      obtain ⟨hr, hm⟩ := hL.modelW _ hj _ hs
      have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := hL.spaceW _ hj _ hs
      have h1 := hm k
      revert hr
      rw [hV]
      exact fun _ _ h => h
    have hε : ∀ a, (R.MW i σ).ε ρ a = decide ((a : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p) := fun a => by
      rw [hF.2 i σ (fun ρ' => (GlobalTheory.HolRead.good_iff_labE_and_lab_conj D T hL hA σ ρ').1.1 hs) ρ a, hdp,
        show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
    rw [key i σ ρ, hM.1, (hU.2.1 k).1]
    exact gram_x0Mat _ _ ρ hU.1 hε
  · have e : x₀ j s τ = T.x₀ j s τ := dif_neg h
    rw [e]
    exact hL.familyUniformisationBasePointOrthogonal j hj s hs k τ hτ

end GlobalTheory.RealGeo.BaseFrame
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalBaseFramesFlagDomainModelsStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_orthonormal_baseFrames_flag_domain_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → AlgTie T → FrameKs T.Q.c.F R.MW → ∃ (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), (∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (x₀ ((i : ℕ) + 1) (res T σ))) ∧ ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ) := by
  first | exact @GlobalTheory.RealGeo.BaseFrame.exists_baseFrame | exact GlobalTheory.RealGeo.BaseFrame.exists_baseFrame | (intros; apply GlobalTheory.RealGeo.BaseFrame.exists_baseFrame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothModelsOnThetaTargetsStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lowest_kType_smooth_models_on_theta_targets : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i σ, LowSm (R.MW i σ) := by
  first | exact @GlobalTheory.LowSmooth.lowSm_MW | exact GlobalTheory.LowSmooth.lowSm_MW | (intros; apply GlobalTheory.LowSmooth.lowSm_MW <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreCompatibleAdelicDataCharacters

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

theorem exists_tieIn_reCore : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → R.toLevCh.Is A.μ0 → ValKs R → FrameKs T.Q.c.F R.MW → ∃ dict mu chiW x₀, TieIn (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) ∧ LawsCore (reCore T dict mu chiW x₀ T.cE).toCore := by
  intro D G _ _ Pl0 T0 A T _ R hvol hJ hC ha hlev hval hfr
  obtain ⟨chiW, hchi, hchi'⟩ := GlobalTheory.T.exists_conjugate_reference_characters_good_embeddings D G Pl0 T0 A T R hJ.pins ha hlev hval
  obtain ⟨x₀, hx, hx'⟩ := GlobalTheory.T.exists_orthonormal_baseFrames_flag_domain_models D G Pl0 T0 A T R hJ ha hfr
  obtain ⟨mu, hJ1, hC1⟩ := GlobalTheory.T.exists_core_laws_for_replaced_hecke_characters D T chiW hJ hC hchi'
  obtain ⟨dict, hJ2, hC2⟩ := GlobalTheory.T.exists_dictionary_core_laws_baseFrame_change D (reCore T T.dict mu chiW T.x₀ T.cE) x₀ hvol hJ1 hC1 hx'
  exact ⟨dict, mu, chiW, x₀, tieIn_top (reCore T dict mu chiW x₀ T.cE) R hJ2 ha
    (GlobalTheory.T.lowest_kType_smooth_models_on_theta_targets D G Pl0 T0 A T.Q.c.F R) hchi hx, hC2⟩

end GlobalTheory.RealGeo
end
end
